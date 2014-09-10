{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ImplicitParams       #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE RecursiveDo          #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}


-- This module implements a hybrid representation of dags, that uses
-- explicit edges only if necessary (i.e. in case of sharing). 

module Dag where

import Control.Applicative
import Control.Exception.Base
import Control.Monad.ST
import Control.Monad.State
import qualified Data.HashMap.Lazy as HashMap
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IORef
import Data.Maybe
import Data.STRef
import Data.Traversable (Traversable)
import qualified Data.Traversable as Traversable
import Data.Typeable
import Data.Vector (MVector, Vector)
import qualified Data.Vector as Vec
import qualified Data.Vector.Generic.Mutable as MVec
import System.Mem.StableName

import AG


-- | The type of node in a 'Dag'.

type Node = Int

-- | The type of the compact edge representation used in a 'Dag'.

type Edges f = IntMap (f (Free f Node))

-- | The type of directed acyclic graphs (DAGs). 'Dag's are used as a
-- compact representation of 'Tree's.

data Dag f = Dag
    { root      :: f (Free f Node) -- ^ the entry point for the DAG
    , edges     :: Edges f         -- ^ the edges of the DAG
    , nodeCount :: Int             -- ^ the total number of nodes in the DAG
    }

-- | Construct a Dag
mkDag :: f (Free f Node) -> [(Node, f (Free f Node))] -> Dag f
mkDag r es = Dag r (IntMap.fromList es) (if null es then 0 else maximum (map fst es) + 1)

-- | This function unravels a given graph to the term it
-- represents.

unravelDag :: forall f. Functor f => Dag f -> Tree f
unravelDag Dag {edges, root} = In $ build <$> root
    where build :: Free f Node -> Tree f
          build (In t) = In $ build <$> t
          build (Ret n) = In $ build <$> edges IntMap.! n

-- | This exception indicates that a 'Tree' could not be reified to a
-- 'Dag' (using 'reifyDag') due to its cyclic sharing structure.
data CyclicException = CyclicException
    deriving (Show, Typeable)

instance Exception CyclicException

-- | This function takes a term, and returns a 'Dag' with the implicit
-- sharing of the input data structure made explicit. If the sharing
-- structure of the term is cyclic an exception of type
-- 'CyclicException' is thrown.
reifyDag :: Traversable f => Tree f -> IO (Dag f)
reifyDag m = do
  tabRef <- newIORef HashMap.empty
  let findNodes (In !j) = do
        st <- liftIO $ makeStableName j
        tab <- readIORef tabRef
        case HashMap.lookup st tab of
          Just (single,f) | single -> writeIORef tabRef (HashMap.insert st (False,f) tab)
                                      >> return st
                          | otherwise -> return st
          Nothing -> do res <- Traversable.mapM findNodes j
                        tab <- readIORef tabRef
                        if HashMap.member st tab
                          then throwIO CyclicException
                          else writeIORef tabRef (HashMap.insert st (True,res) tab)
                               >> return st
  st <- findNodes m
  tab <- readIORef tabRef
  counterRef <- newIORef 0
  edgesRef <- newIORef IntMap.empty
  nodesRef <- newIORef HashMap.empty
  let run st = do
        let (single,f) = tab HashMap.! st
        if single then In <$> Traversable.mapM run f
        else do
          nodes <- readIORef nodesRef
          case HashMap.lookup st nodes of
            Just n -> return (Ret n)
            Nothing -> do
              n <- readIORef counterRef
              writeIORef counterRef $! (n+1)
              writeIORef nodesRef (HashMap.insert st n nodes)
              f' <- Traversable.mapM run f
              modifyIORef edgesRef (IntMap.insert n f')
              return (Ret n)
  In root <- run st
  edges <- readIORef edgesRef
  count <- readIORef counterRef
  return (Dag root edges count)


-- | This function runs an AG on a dag.
runAGDag :: forall f d u .Traversable f
    => (d -> d -> d)   -- ^ Resolution of top-down state
    -> Syn' f (u,d) u  -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d  -- ^ Top-down state propagation
    -> (u -> d)         -- ^ Initial top-down state
    -> Dag f
    -> u
runAGDag res syn inh dinit g = u
    where d = dinit u
          syn' :: SynExpl f (u,d) u
          syn' = explicit syn
          inh' :: InhExpl f (u,d) d
          inh' = explicit inh
          run = free res  syn' inh'
          (u,dmapRoot) = run d umap (root g)
          dmap = IntMap.foldr (\ (_,m1) m2 -> IntMap.unionWith res m1 m2)
                 dmapRoot result
          umap = IntMap.map fst result
          result = IntMap.mapWithKey (\ n t -> run (dmap IntMap.! n) umap t) (edges g)


-- | Auxiliary function for 'runAGDag'.

free :: forall f u d . Traversable f => (d -> d -> d) -> SynExpl f (u,d) u -> InhExpl f (u,d) d
     -> d -> IntMap u -> f (Free f Node) -> (u, IntMap d)
free res syn inh d umap s = run d s where
    run :: d -> f (Free f Node) -> (u, IntMap d)
    run d t = (u, dmap)
        where u = syn (u,d) unNumbered result
              m = inh (u,d) unNumbered result
              (result, (dmap,_)) = runState (Traversable.mapM run' t) (IntMap.empty,0)
              run' :: Free f Node -> State (IntMap d, Int) (Numbered ((u,d)))
              run' s = do
                  (oldDmap,i) <- get
                  let d' = lookupNumMap d i m
                      (u',dmap') = runF d' s
                  put (IntMap.unionWith res dmap' oldDmap, (i+1))
                  return (Numbered i (u',d'))
    runF :: d -> Free f Node -> (u, IntMap d)
    runF d (Ret x) = (umap IntMap.! x, IntMap.singleton x d)
    runF d (In t)  = run d t

-- | This function runs an attribute grammar on a dag. The result is
-- the (combined) synthesised attribute at the root of the dag.

runAGDagST :: forall f d u .Traversable f
    => (d -> d -> d)   -- ^ resolution function for inherited attributes
    -> Syn' f (u,d) u  -- ^ semantic function of synthesised attributes
    -> Inh' f (u,d) d  -- ^ semantic function of inherited attributes
    -> (u -> d)        -- ^ initialisation of inherited attributes
    -> Dag f           -- ^ input dag
    -> u
runAGDagST _ syn inh dinit Dag {root = t,nodeCount=0} = uFin where
    dFin = dinit uFin
    uFin = run dFin t 
    run d t = u where
        t' = fmap bel $ number t
        bel (Numbered i s) =
            let d' = lookupNumMap d i m
            in Numbered i (run' d' s, d')
        m = explicit inh (u,d) unNumbered t'
        u = explicit syn (u,d) unNumbered t'
    run' _ (Ret _) = error "runAGDagST: the input dag has no edges!"
    run' d (In t) = run d t

runAGDagST res syn inh dinit Dag {edges,root,nodeCount} = uFin where
    uFin = runST runM
    dFin = dinit uFin
    runM :: forall s . ST s u
    runM = mdo
      -- construct empty mapping from nodes to inherited attribute values
      dmap <- MVec.new nodeCount
      MVec.set dmap Nothing
      -- allocate mapping from nodes to synthesised attribute values
      umap <- MVec.new nodeCount
      -- allocate counter for numbering child nodes
      count <- newSTRef 0
      let -- Runs the AG on an edge with the given input inherited
          -- attribute value and produces the output synthesised
          -- attribute value.
          run :: d -> f (Free f Node) -> ST s u
          run d t = mdo
             -- apply the semantic functions
             let u = explicit syn (u,d) unNumbered result
                 m = explicit inh (u,d) unNumbered result
                 -- recurses into the child nodes and numbers them
                 run' :: Free f Node -> ST s (Numbered (u,d))
                 run' s = do i <- readSTRef count
                             writeSTRef count $! (i+1)
                             let d' = lookupNumMap d i m
                             u' <- runF d' s -- recurse
                             return (Numbered i (u',d'))
             writeSTRef count 0  -- re-initialize counter
             result <- Traversable.mapM run' t
             return u
          -- recurses through the tree structure
          runF :: d -> Free f Node -> ST s u
          runF d (Ret x) = do
             -- we found a node: update the mapping for inherited
             -- attribute values
             old <- MVec.unsafeRead dmap x
             let new = case old of
                         Just o -> res o d
                         _      -> d
             MVec.unsafeWrite dmap x (Just new)
             return (umapFin Vec.! x)
          runF d (In t)  = run d t
          -- This function is applied to each edge
          iter (n, t) = do
            u <- run (fromJust $ dmapFin Vec.! n) t
            MVec.unsafeWrite umap n u
      -- first apply to the root
      u <- run dFin root
      -- then apply to the edges
      mapM_ iter (IntMap.toList edges)
      -- finalise the mappings for attribute values
      dmapFin <- Vec.unsafeFreeze dmap
      umapFin <- Vec.unsafeFreeze umap
      return u

-- | This function runs an attribute grammar with rewrite function on
-- a dag. The result is the (combined) synthesised attribute at the
-- root of the dag and the rewritten dag.

runRewriteDagST :: forall f g d u .(Traversable f, Traversable g)
    => (d -> d -> d)       -- ^ resolution function for inherited attributes
    -> Syn' f (u,d) u      -- ^ semantic function of synthesised attributes
    -> Inh' f (u,d) d      -- ^ semantic function of inherited attributes
    -> Rewrite f (u, d) g  -- ^ initialisation of inherited attributes
    -> (u -> d)            -- ^ input term
    -> Dag f
    -> (u, Dag g)
runRewriteDagST _ syn inh rewr dinit Dag {root=t,nodeCount=0} 
             = (uFin,Dag{root= norm res, edges=IntMap.empty,nodeCount=0}) where
    dFin = dinit uFin
    (uFin,res) = run dFin t
    norm (In t) = t
    norm (Ret _) =  error "runRewriteDagST: the input dag has no edges!"
    run' _ (Ret _) = error "runRewriteDagST: the input dag has no edges!"
    run' d (In t) = run d t
    run d t = (u,t'') where
        t' = fmap bel $ number t
        bel (Numbered i s) =
            let d' = lookupNumMap d i m
                (u', s') = run' d' s
            in Numbered i ((u', d'),s')
        m = explicit inh (u,d) (fst . unNumbered) t'
        u = explicit syn (u,d) (fst . unNumbered) t'
        t'' = join $ fmap (snd . unNumbered) $ explicit rewr (u,d) (fst . unNumbered) t'
runRewriteDagST res syn inh rewr dinit Dag {edges,root,nodeCount} = result where
    result@(uFin,_) = runST runM
    dFin = dinit uFin
    runM :: forall s . ST s (u, Dag g)
    runM = mdo
      -- construct empty mapping from nodes to inherited attribute values
      dmap <- MVec.new nodeCount
      MVec.set dmap Nothing
      -- allocate mapping from nodes to synthesised attribute values
      umap <- MVec.new nodeCount
      -- allocate counter for numbering child nodes
      count <- newSTRef 0
      -- allocate vector to represent edges of the target DAG
      allEdges <- MVec.new nodeCount
      let -- This function is applied to each edge
          iter (node,s) = do
             let d = fromJust $ dmapFin Vec.! node
             (u,t) <- run d s
             MVec.unsafeWrite umap node u
             MVec.unsafeWrite allEdges node t
          -- Runs the AG on an edge with the given input inherited
          -- attribute value and produces the output synthesised
          -- attribute value along with the rewritten subtree.
          run :: d -> f (Free f Node) -> ST s (u, Free g Node)
          run d t = mdo
             -- apply the semantic functions
             let u = explicit syn (u,d) (fst . unNumbered) result
                 m = explicit inh (u,d) (fst . unNumbered) result
                 -- recurses into the child nodes and numbers them
                 run' :: Free f Node -> ST s (Numbered ((u,d), Free g Node))
                 run' s = do i <- readSTRef count
                             writeSTRef count $! (i+1)
                             let d' = lookupNumMap d i m
                             (u',t) <- runF d' s
                             return (Numbered i ((u',d'), t))
             writeSTRef count 0
             result <- Traversable.mapM run' t
             let t' = join $ fmap (snd . unNumbered) $ explicit rewr (u,d) (fst . unNumbered) result
             return (u, t')
          -- recurses through the tree structure
          runF d (In t) = run d t
          runF d (Ret x) = do
             -- we found a node: update the mapping for inherited
             -- attribute values
             old <- MVec.unsafeRead dmap x
             let new = case old of
                         Just o -> res o d
                         _      -> d
             MVec.unsafeWrite dmap x (Just new)
             return (umapFin Vec.! x, Ret x)
      -- first apply to the root
      (u,interRoot) <- run dFin root
      -- then apply to the edges
      mapM_ iter $ IntMap.toList edges
      -- finalise the mappings for attribute values and target DAG
      dmapFin <- Vec.unsafeFreeze dmap
      umapFin <- Vec.unsafeFreeze umap
      allEdgesFin <- Vec.unsafeFreeze allEdges
      return (u, relabelNodes interRoot allEdgesFin nodeCount)


-- | This function relabels the nodes of the given dag. Parts that are
-- unreachable from the root are discarded. Instead of an 'IntMap',
-- edges are represented by a 'Vector'.
relabelNodes :: forall f . Traversable f
             => Free f Node
             -> Vector (Free f Int)
             -> Int
             -> Dag f
relabelNodes root edges nodeCount = runST run where
    run :: ST s (Dag f)
    run = do
      -- allocate counter for generating nodes
      curNode <- newSTRef 0
      newEdges <- newSTRef IntMap.empty  -- the new dag
      -- construct empty mapping for mapping old nodes to new nodes
      newNodes :: MVector s (Maybe Int) <- MVec.new nodeCount
      MVec.set newNodes Nothing
      let -- Replaces node in the old dag with a node in the new
          -- dag. This function is applied to all nodes reachable
          -- from the given node as well.
          build :: Node -> ST s Node
          build node = do
            -- check whether we have already constructed a new node
            -- for the given node
             mnewNode <- MVec.unsafeRead newNodes node
             case mnewNode of
               Just newNode -> return newNode
               Nothing ->
                   case edges Vec.! node of
                     Ret n -> do
                       -- We found an edge that just maps to another
                       -- node. We shortcut this edge.
                       newNode <- build n
                       MVec.unsafeWrite newNodes node (Just newNode)
                       return newNode
                     In f -> do
                        -- Create a new node and call build recursively
                       newNode <- readSTRef curNode
                       writeSTRef curNode $! (newNode+1)
                       MVec.unsafeWrite newNodes node (Just newNode)
                       f' <- Traversable.mapM (Traversable.mapM build) f
                       modifySTRef newEdges (IntMap.insert newNode f')
                       return newNode
          -- This function is only used for the root. If the root is
          -- only a node, we lookup the mapping for that
          -- node. In any case we apply build to all nodes.
          build' :: Free f Node -> ST s (f (Free f Node))
          build' (Ret n) = do
                         n' <- build n
                         e <- readSTRef newEdges
                         return (e IntMap.! n')
          build' (In f) = Traversable.mapM (Traversable.mapM build) f
      -- start relabelling from the root
      root' <- build' root
      -- collect the final edges mapping and node count
      edges' <- readSTRef newEdges
      nodeCount' <- readSTRef curNode
      return Dag {edges = edges', root = root', nodeCount = nodeCount'}


termTree :: Functor f => Tree f -> Dag f
termTree (In t) = Dag (fmap freeTree t) (IntMap.empty) 0
