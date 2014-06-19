{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecursiveDo #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Graph
-- Copyright   :  (c) 2012 Patrick Bahr
-- License     :  BSD3
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--
--------------------------------------------------------------------------------

-- Original copied from the "graph" branch at <https://bitbucket.org/paba/compdata>

module Graph
    ( module AG
    , Graph (..)
    , GraphFree
    , Node
    , termTree
    , termTreeFree
    , unravelGraph
    , appGraphCxt
    , reifyGraph
    , reifyDAG
    , graphCata
    , graphEdges
    , lookupNode

    , mkGraph
    , liftGraph
    , image
    , reachable
    , removeOrphans
    , reindexGraph
    , appCxtGraph
    , runRewriteGraph
    , runRewriteGraph'
    , runAGGraph
    , runAGGraph'
    , runAGGraphST
    , runAGGraphFree
    , runAGGraphFreeST
    ) where

import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import qualified Data.Map as Map
import Data.Traversable (Traversable)
import qualified Data.Traversable as Traversable
import Data.List (intercalate)
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.Error
import System.Mem.StableName


import Control.Monad.ST
import Data.STRef
import qualified Data.Vector as Vec
import qualified Data.Vector.Generic.Mutable as MVec
import Data.Maybe

import Safe

import AG


type Node = Int

-- | This type represents graphs over a given signature with a
-- distinguished root node. Such graphs, also known as term graphs,
-- represent terms. This representation is given by the unravelling
-- operation (cf. 'unravelGraph').
data Graph f = Graph { _root :: Node
                     , _eqs :: IntMap (f Node)
                     , _next :: Node }

type GraphFree f = Graph (Free f)

data GraphCxt f a = GraphCxt { _graph :: Graph f
                             , _holes :: IntMap a }

graphEdges :: Graph f -> IntMap (f Node)
graphEdges = _eqs

type AppT f = (Node, IntMap Node, [(Node, f Node)])

appGraphCxt :: forall f . (Functor f) => GraphCxt f (Graph f) -> Graph f
appGraphCxt (GraphCxt (Graph root eqs nx) (holes)) = Graph root' eqs' nx'
    where run :: Node -> Graph f -> AppT f -> AppT f
          run n (Graph r e nx) (next,rename,neweqs) =
              (next+nx,
               IntMap.insert n (r+next) rename,
               [(left + next, fmap (+next) right) | (left , right ) <- IntMap.toList e] ++ neweqs)
          init :: AppT g
          init = (nx,IntMap.empty, [])
          (nx',rename,new)= IntMap.foldrWithKey run init holes
          renameFun :: Node -> Node
          renameFun n = IntMap.findWithDefault n n rename
          eqs' = foldl (\ m (k,v) -> IntMap.insert k v m) (IntMap.map (fmap renameFun) eqs) new
          root' = renameFun root

-- | This function turns a term into a graph without (explicit)
-- sharing, i.e. a tree. The following property holds for 'termTree'
-- and 'unravelGraph':
-- 
-- @
-- unravelGraph (termTree x) == x
-- @
termTree :: Traversable f => Tree f -> Graph f
termTree t = Graph 0 imap nx
    where (imap,nx) = runState (liftM snd $ runWriterT $ build t) 0
          build :: Traversable f => Tree f -> WriterT (IntMap (f Node)) (State Node) Node
          build (In t) = do n <- get
                            put (n+1)
                            res <- Traversable.mapM build t
                            tell $ IntMap.singleton n res
                            return n

-- | This function unravels a given graph to the term it
-- represents. The following property holds for 'termTree' and
-- 'unravelGraph':
-- 
-- @
-- unravelGraph (termTree x) == x
-- @
unravelGraph :: forall f. Functor f => Graph f -> Tree f
unravelGraph g = build (_root g)
    where build :: Node -> Tree f
          build n = In $ fmap build $ lookupNode n (graphEdges g)

type Alg f c = f c -> c

graphCata :: forall f c . Functor f => Alg f c -> Graph f -> c
graphCata alg g = run (_root g)
    where run :: Node -> c
          run n = alg $ fmap run $ lookupNode n (graphEdges g)

-- | Internal function used to lookup the nodes in a graph. It assumes
-- a node of a graph that is either the root node or a target node of
-- one of the edges. The implementation of this function makes use of
-- the invariant that each such node must also be in the domain of the
-- IntMap of the graph.
lookupNode :: Node -> IntMap (f Node) -> f Node
lookupNode n imap = fromJustNote "edge leading to an undefined node" $ IntMap.lookup n imap

-- | This function takes a term, and returns a 'Graph' with the
-- implicit sharing of the input data structure made explicit.
reifyGraph :: Traversable f => Tree f -> IO (Graph f)
reifyGraph m = do (root, state) <- runStateT (findNodes m) init
                  return (Graph root (rsEqs state) (rsNext state))
    where  init = ReifyState
                  { rsStable = HashMap.empty
                  , rsEqs = IntMap.empty
                  , rsNext = 0 }

data ReifyState f = ReifyState
    { rsStable :: HashMap (StableName (f (Tree f))) Node
    , rsEqs :: IntMap (f Node)
    , rsNext :: Node
    }

findNodes :: Traversable f => Tree f -> StateT (ReifyState f) IO Node
findNodes (In !j) = do
        st <- liftIO $ makeStableName j
        tab <- liftM rsStable get
        case HashMap.lookup st tab of
          Just var -> return $ var
          Nothing -> do var <- liftM rsNext get
                        modify (\s -> s{ rsNext = var + 1
                                       , rsStable = HashMap.insert st var tab})
                        res <- Traversable.mapM findNodes j
                        modify (\s -> s { rsEqs = IntMap.insert var res (rsEqs s)})
                        return var


-- | This function takes a term, and returns a 'Graph' with the
-- implicit sharing of the input data structure made
-- explicit. Moreover it checks that the constructed graph is acyclic
-- and only returns the graph it is acyclic.
reifyDAG :: Traversable f => Tree f -> IO (Maybe (Graph f))
reifyDAG m = do res <- runErrorT (runStateT (runReaderT (findNodes' m) HashSet.empty) init)
                case res of 
                  Left _ -> return Nothing
                  Right (root, state) ->return (Just (Graph root (rsEqs state) (rsNext state)))
    where  init = ReifyState
                  { rsStable = HashMap.empty
                  , rsEqs = IntMap.empty
                  , rsNext = 0 }


findNodes' :: Traversable f => Tree f -> 
              ReaderT (HashSet (StableName (f (Tree f))))  
               (StateT (ReifyState f) (ErrorT String IO)) Node
findNodes' (In !j) = do
        st <- liftIO $ makeStableName j
        seen <- ask
        when (HashSet.member st seen) (throwError "")
        tab <- liftM rsStable get
        case HashMap.lookup st tab of
          Just var -> return $ var
          Nothing -> do var <- liftM rsNext get
                        modify (\s -> s{ rsNext = var + 1
                                       , rsStable = HashMap.insert st var tab})
                        res <- local (HashSet.insert st) (Traversable.mapM findNodes' j)
                        modify (\s -> s { rsEqs = IntMap.insert var res (rsEqs s)})
                        return var



instance (Show (f String), Functor f) => Show (Graph f)
  where
    show (Graph r es _) = unwords
        [ "mkGraph"
        , show r
        , showLst ["(" ++ show n ++ "," ++ show (fmap show f) ++ ")" | (n,f) <- IntMap.toList es ]
        ]
      where
        showLst ss = "[" ++ intercalate "," ss ++ "]"

-- | Construct a graph
mkGraph :: Node -> [(Node, f Node)] -> Graph f
mkGraph r es = Graph r (IntMap.fromList es) (maximum (map fst es) + 1)

-- | Lift an 'IntMap.IntMap' operation to a 'Graph'. Assumes that the function does not affect the
-- set of keys.
liftGraph :: (Node -> IntMap (f Node) -> IntMap (g Node)) -> Graph f -> Graph g
liftGraph f (Graph r es nx) = Graph r (f r es) nx

-- | Fixed-point iteration
fixedpoint :: Eq a => (a -> a) -> (a -> a)
fixedpoint f a
    | a == fa   = a
    | otherwise = fixedpoint f fa
  where
    fa = f a

-- | Makes a set operation monotonous
mkMonot :: (IntSet -> IntSet) -> (IntSet -> IntSet)
mkMonot f a = a `IntSet.union` f a

-- | Computes the image of a set of nodes
image :: Foldable f => IntMap (f Node) -> IntSet -> IntSet
image es ns = IntSet.fromList $ concatMap (Foldable.toList . (es IntMap.!)) $ IntSet.toList ns

-- | Computes the set of nodes reachable from the root. This function is not very efficient.
-- Something like @(n^2 log n)@.
reachable :: Foldable f => Node -> IntMap (f Node) -> IntSet
reachable n es = fixedpoint (mkMonot (image es)) (IntSet.singleton n)

-- | Removes orphan nodes from a graph
removeOrphans :: Foldable f => Node -> IntMap (f Node) -> IntMap (f Node)
removeOrphans r es = IntMap.fromSet (es IntMap.!) rs
  where
    rs = reachable r es

-- | Make an equivalent graph using consecutive indexes form 0 and up
reindexGraph :: Functor f => Graph f -> Graph f
reindexGraph (Graph r es nx) = Graph (reix r) es' nx'
  where
    (ns,fs) = unzip $ IntMap.toList es
    reix    = (IntMap.!) (IntMap.fromList (zip ns [0..]))
    es'     = IntMap.fromAscList $ zip [0..] $ map (fmap reix) fs
    nx'     = length ns

data Indirect f a
    = Indirect Node
    | Direct (f a)
  deriving (Eq, Show, Functor)

direct :: Indirect f a -> Maybe (f a)
direct (Direct f) = Just f
direct _          = Nothing

chase :: IntMap (Indirect f a) -> Node -> Node
chase es n = case es IntMap.! n of
    Indirect n' -> chase es n'
    _ -> n

removeIndirections :: Functor f => Graph (Indirect f) -> Graph f
removeIndirections (Graph r es nx) = Graph (chase es r) es' nx
  where
    es' = IntMap.mapMaybe direct $ fmap (fmap (chase es)) es

freshNode :: MonadState Node m => m Node
freshNode = do
    n <- get
    put (succ n)
    return n

-- | Turn a 'Free' into an association list each node has a freshly generated identifier
listCxt :: Traversable f => Free f Node -> WriterT [(Node, f Node)] (State Node) Node
listCxt (Ret n) = return n
listCxt (In f) = do
    n  <- freshNode
    f' <- Traversable.mapM listCxt f
    tell [(n,f')]
    return n

-- | Turn a 'Free' into an association list where the provided node @n@ maps to the root of the
-- context
listCxtTop :: Traversable f =>
    Node -> Free f Node -> WriterT [(Node, Indirect f Node)] (State Node) ()
listCxtTop n (Ret n') = tell [(n, Indirect n')]
listCxtTop n (In f)  = do
    (f',es) <- lift $ runWriterT $ Traversable.mapM listCxt f
    tell [(n, Direct f')]
    tell $ map (\(n,f) -> (n, Direct f)) es

-- | Joining a graph of contexts. The node identifiers in the resulting graph are unrelated to those
-- in the original graph.
appCxtGraph :: Traversable f => Graph (Free f) -> Graph f
appCxtGraph g = removeIndirections $ Graph r (IntMap.fromList es') nx'
  where
    Graph r es nx = reindexGraph g
    (es',nx')     = flip runState nx
                  $ execWriterT
                  $ Traversable.mapM (uncurry listCxtTop)
                  $ IntMap.assocs
                  $ es

mapGraphM :: Monad m => (Node -> f Node -> m (g Node)) -> Graph f -> m (Graph g)
mapGraphM f g = do
    es <- Traversable.sequence $ IntMap.mapWithKey f $ graphEdges g
    return g {_eqs = es}

fromListEither :: (a -> a -> a) -> (b -> b -> b) -> [(Int, Either a b)] -> IntMap (a,b)
fromListEither fa fb as = IntMap.fromList [(i,(am IntMap.! i, bm IntMap.! i)) | i <- is]
  where
    is = IntMap.keys $ IntMap.fromList as
    am = IntMap.fromListWith fa [(i,a) | (i, Left a)  <- as]
    bm = IntMap.fromListWith fb [(i,b) | (i, Right b) <- as]

dropNumber :: Numbered a -> a
dropNumber (Numbered (_,a)) = a


runRewriteGraph :: forall f g u d . (Traversable f, Functor g, Traversable g)
    => (d -> d -> d)          -- ^ Resolution of downwards state
    -> Syn'    f (u, d) u  -- ^ Bottom-up state propagation
    -> Inh'    f (u, d) d  -- ^ Top-down state propagation
    -> Rewrite f (u, d) g  -- ^ Homomorphic rewrite
    -> d                      -- ^ Initial top-down state
    -> Graph f                -- ^ Original term
    -> (u, Graph g)           -- ^ Final state and rewritten term
runRewriteGraph res up down rew d g = (fst $ env $ _root g, appCxtGraph gg)
  where
    (gg,ws) = runWriter $ mapGraphM rewNode g
    ws'     = (_root g, Right d) : ws
    env n   = fromListEither errUp res ws' IntMap.! n
    errUp   = error "runRewriteGraph1: over-constrained bottom-up state"

    rewNode :: Node -> f Node -> Writer [(Node, Either u d)] (Free g Node)
    rewNode n f = do
        tell [(n, Left (up f))]
        let dm = down f
        Traversable.forM f $ \n -> tell [(n, Right (Map.findWithDefault (snd ?above) n dm))]
        return (rew f)
      where
        ?above = env n
        ?below = env

runRewriteGraph' :: forall f g u d . (Traversable f, Functor g, Traversable g)
    => (d -> d -> d)          -- ^ Resolution of downwards state
    -> Syn'    f (u, d) u  -- ^ Bottom-up state propagation
    -> Inh'    f (u, d) d  -- ^ Top-down state propagation
    -> Rewrite f (u, d) g  -- ^ Homomorphic rewrite
    -> (u -> d)            -- ^ Initial top-down state
    -> Graph f                -- ^ Original term
    -> (u, Graph g)           -- ^ Final state and rewritten term
runRewriteGraph' res up down rew d' g = (u, g')
    where (u, g') = runRewriteGraph res up down rew d g
          d       = d' u

-- -- For reference, runUpState from compdata
-- runUpState1 :: Functor f => UpState f q -> Term f -> q
-- runUpState1 up = go
--   where
--     go = up . fmap go . unTerm

-- -- No memoization
-- runUpStateGraph1 :: Functor f => UpState f q -> Graph f -> q
-- runUpStateGraph1 up g = go (_root g)
--   where
--     go = up . fmap go . (graphEdges g IntMap.!)

-- -- With memoization
-- runUpStateGraph :: Functor f => UpState f q -> Graph f -> q
-- runUpStateGraph up g = goMem (_root g)
--   where
--     states = IntMap.mapWithKey (\n _ -> go n) $ graphEdges g
--     goMem  = (states IntMap.!)
--     go     = up . fmap goMem . (graphEdges g IntMap.!)

-- -- With memoization (fewer lookups)
-- runUpStateGraphAlt :: Functor f => UpState f q -> Graph f -> q
-- runUpStateGraphAlt up g = states IntMap.! _root g
--   where
--     states = fmap (up . fmap (states IntMap.!)) (graphEdges g)

-- | Run a bottom-up state automaton over a graph, resulting in a map containing the up state for
-- each node. The global environment must be defined for all nodes in the graph.
runSynGraph
    :: Syn' f (u,d) u  -- Bottom-up state propagation
    -> (Node -> (u,d))     -- Global environment containing the state of each node
    -> Graph f
    -> IntMap u
runSynGraph up env = IntMap.mapWithKey (\n -> explicit up (env n) env) . graphEdges

-- | Run a top-down state automaton over a graph, resulting in a map containing the down state for
-- each node. The global environment must be defined for all nodes in the graph.
runInhGraph :: forall f u d . Traversable f
    => (d -> d -> d)         -- Resolution of top-down state
    -> Inh' f (u,d) d  -- Top-down state propagation
    -> d                     -- Initial top-down state
    -> (Node -> (u,d))       -- Global environment containing the state of each node
    -> Graph f
    -> IntMap d
runInhGraph res down d env g = IntMap.fromListWith res
    $ ((_root g, d):)
    $ concatMap (uncurry downNode)
    $ IntMap.toList
    $ fmap number
    $ graphEdges g
  where
    downNode :: (Functor f, Foldable f) => Node -> f (Numbered Node) -> [(Node,d)]
    downNode n f = Foldable.toList $ fmap (\a -> (dropNumber a, Map.findWithDefault (snd $ env n) a dm)) f
      where
        dm = explicit down (env n) (env . dropNumber) f

-- | Run a bidirectional state automaton over a term graph
runAGGraph :: Traversable f
    => (d -> d -> d)         -- ^ Resolution of top-down state
    -> Syn' f (u,d) u  -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d  -- ^ Top-down state propagation
    -> d                     -- ^ Initial top-down state
    -> Graph f
    -> u
runAGGraph res up down d g = envU IntMap.! _root g
  where
    envU  = runSynGraph up env g
    envD  = runInhGraph res down d env g
    env n = (envU IntMap.! n, envD IntMap.! n)


runAGGraph' :: Traversable f => (d -> d -> d) -> Syn' f (u,d) u -> Inh' f (u,d) d -> (u -> d) -> Graph f -> u
runAGGraph' res syn inh df g = let u = runAGGraph res syn inh d g
                                   d = df u
                               in u

runAGGraphFree :: forall f d u .Traversable f
    => (d -> d -> d)         -- ^ Resolution of top-down state
    -> Syn' f (u,d) u  -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d  -- ^ Top-down state propagation
    -> d                     -- ^ Initial top-down state
    -> GraphFree f
    -> u
runAGGraphFree res syn inh d g = umap IntMap.! _root g
    where syn' :: SynExpl f (u,d) u
          syn' = explicit syn
          inh' :: InhExpl f (u,d) d
          inh' = explicit inh
          run = free res  syn' inh'
          dmap = IntMap.foldr (\ (_,m1) m2 -> IntMap.unionWith res m1 m2) 
                 (IntMap.singleton (_root g) d) result
          umap = IntMap.map fst result
          result = IntMap.mapWithKey (\ n t -> run (dmap IntMap.! n) umap t) (_eqs g)




free :: forall f u d . Traversable f => (d -> d -> d) -> SynExpl f (u,d) u -> InhExpl f (u,d) d
     -> d -> IntMap u -> Free f Node -> (u, IntMap d)
free res syn inh d umap s = run d s where
    run :: d -> Free f Node -> (u, IntMap d)
    run d (Ret x) = (umap IntMap.! x, IntMap.singleton x d)
    run d (In t)  = (u, dmap)
        where u = syn (u,d) unNumbered result
              m = inh (u,d) unNumbered result
              (result, (dmap,_)) = runState (Traversable.mapM run' t) (IntMap.empty,0)
              run' :: Free f Node -> State (IntMap d, Int) (Numbered ((u,d)))
              run' s = do
                  (oldDmap,i) <- get
                  let d' = Map.findWithDefault d (Numbered (i,undefined)) m
                      (u',dmap') = run d' s
                  put (IntMap.unionWith res dmap' oldDmap, (i+1))
                  return (Numbered (i, (u',d')))

runAGGraphFreeST :: forall f d u .Traversable f
    => (d -> d -> d)         -- ^ Resolution of top-down state
    -> Syn' f (u,d) u  -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d  -- ^ Top-down state propagation
    -> d                     -- ^ Initial top-down state
    -> GraphFree f
    -> u
runAGGraphFreeST res syn inh d g = runST runM 
    where syn' :: SynExpl f (u,d) u
          syn' = explicit syn
          inh' :: InhExpl f (u,d) d
          inh' = explicit inh
          runM :: ST s u
          runM = mdo dmap <- MVec.new (_next g)
                     MVec.set dmap Nothing
                     MVec.write dmap (_root g) (Just d)
                     umap <- MVec.new (_next g)
                     let iter (n, t) = do 
                           u <- freeST res  syn' inh' dmap (fromJust $ dmapFin Vec.! n) umapFin t   
                           MVec.write umap n u
                           return ()
                     mapM_ iter (IntMap.toList $ _eqs g)
                     dmapFin <- Vec.unsafeFreeze dmap
                     umapFin <- Vec.unsafeFreeze umap
                     return (umapFin Vec.! _root g)





freeST :: forall f u d s . Traversable f => (d -> d -> d) -> SynExpl f (u,d) u -> InhExpl f (u,d) d
       -> Vec.MVector s (Maybe d)
     -> d -> Vec.Vector u -> Free f Node -> ST s u
freeST res syn inh ref d umap s = run d s where
    run :: d -> Free f Node -> ST s u
    run d (Ret x) = do old <- MVec.unsafeRead ref x
                       let new = case old of
                                   Just o -> res o d
                                   _      -> d
                       MVec.unsafeWrite ref x (Just new)
                       return (umap Vec.! x)
    run d (In t)  = mdo let u = syn (u,d) unNumbered result
                        let m = inh (u,d) unNumbered result
                        count <- newSTRef 0
                        let run' :: Free f Node -> ST s (Numbered (u,d))
                            run' s = do i <- readSTRef count
                                        writeSTRef count (i+1)
                                        let d' = Map.findWithDefault d (Numbered (i,undefined)) m
                                        u' <- run d' s
                                        return (Numbered (i, (u',d')))
                        result <- Traversable.mapM run' t
                        return u


termTreeFree :: Functor f => Tree f -> GraphFree f
termTreeFree t = Graph 0 (IntMap.singleton 0 (freeTree t)) 1

runAGGraphST :: forall f d u .Traversable f
    => (d -> d -> d)         -- ^ Resolution of top-down state
    -> Syn' f (u,d) u  -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d  -- ^ Top-down state propagation
    -> d                     -- ^ Initial top-down state
    -> Graph f
    -> u
runAGGraphST res syn inh d g = runST runM 
    where syn' :: SynExpl f (u,d) u
          syn' = explicit syn
          inh' :: InhExpl f (u,d) d
          inh' = explicit inh
          runM :: ST s u
          runM = mdo dmap <- MVec.new (_next g)
                     MVec.set dmap Nothing
                     MVec.write dmap (_root g) (Just d)
                     umap <- MVec.new (_next g)
                     let iter (n, t) = do 
                           u <- runDownST res  syn' inh' dmap (fromJust $ dmapFin Vec.! n) umapFin t   
                           MVec.write umap n u
                           return ()
                     mapM_ iter (IntMap.toList $ _eqs g)
                     dmapFin <- Vec.unsafeFreeze dmap
                     umapFin <- Vec.unsafeFreeze umap
                     return (umapFin Vec.! _root g)



runDownST :: forall f u d s . Traversable f => (d -> d -> d) -> SynExpl f (u,d) u -> InhExpl f (u,d) d
       -> Vec.MVector s (Maybe d)
     -> d -> Vec.Vector u -> f Node -> ST s u
runDownST res syn inh ref d umap s = run d s where
    runArg :: d -> Node -> ST s u
    runArg d x = do old <- MVec.unsafeRead ref x
                    let new = case old of
                                Just o -> res o d
                                _      -> d
                    MVec.unsafeWrite ref x (Just new)
                    return (umap Vec.! x)
    run :: d -> f Node -> ST s u
    run d t  = mdo let u = syn (u,d) unNumbered result
                   let m = inh (u,d) unNumbered result
                   count <- newSTRef 0
                   let run' :: Node -> ST s (Numbered (u,d))
                       run' s = do i <- readSTRef count
                                   writeSTRef count (i+1)
                                   let d' = Map.findWithDefault d (Numbered (i,undefined)) m
                                   u' <- runArg d' s
                                   return (Numbered (i, (u',d')))
                   result <- Traversable.mapM run' t
                   return u
