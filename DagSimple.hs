{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ImplicitParams         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE RecursiveDo            #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}


-- Naive representation of dags.

module DagSimple
    ( module AG
    , Dag (..)
    , Node
    , termTree
    , unravelDag
    , reifyDag
    , lookupNode
    , mkDag
    , liftDag
    , image
    , reachable
    , removeOrphans
    , reindexDag
    , appCxtDag
    , runRewriteDag
    , runRewriteDagST
    , runAGDag
    , runAGDagST
    ) where

import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap


import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet


import Control.Monad.State
import Control.Monad.Writer
import Data.List (intercalate)
import Data.Traversable (Traversable)
import qualified Data.Traversable as Traversable


import System.Mem.StableName


import Control.Monad.ST
import Data.Maybe
import Data.STRef
import qualified Data.Vector as Vec
import qualified Data.Vector.Generic.Mutable as MVec

import Safe

import AG


type Node = Int

-- | This type represents dags over a given signature with a
-- distinguished root node. Such dags, also known as term dags,
-- represent terms. This representation is given by the unravelling
-- operation (cf. 'unravelDag').
data Dag f = Dag { root          :: Node
                     , edges     :: IntMap (f Node)
                     , nodeCount :: Node }


-- | This function turns a term into a dag without (explicit)
-- sharing, i.e. a tree. The following property holds for 'termTree'
-- and 'unravelDag':
--
-- @
-- unravelDag (termTree x) == x
-- @
termTree :: Traversable f => Tree f -> Dag f
termTree t = Dag 0 imap nx
    where (imap,nx) = runState (liftM snd $ runWriterT $ build t) 0
          build :: Traversable f => Tree f -> WriterT (IntMap (f Node)) (State Node) Node
          build (In t) = do n <- get
                            put (n+1)
                            res <- Traversable.mapM build t
                            tell $ IntMap.singleton n res
                            return n

-- | This function unravels a given dag to the term it
-- represents. The following property holds for 'termTree' and
-- 'unravelDag':
--
-- @
-- unravelDag (termTree x) == x
-- @
unravelDag :: forall f. Functor f => Dag f -> Tree f
unravelDag g = build (root g)
    where build :: Node -> Tree f
          build n = In $ fmap build $ lookupNode n (edges g)

-- | Internal function used to lookup the nodes in a dag. It assumes
-- a node of a dag that is either the root node or a target node of
-- one of the edges. The implementation of this function makes use of
-- the invariant that each such node must also be in the domain of the
-- IntMap of the dag.
lookupNode :: Node -> IntMap (f Node) -> f Node
lookupNode n imap = fromJustNote "edge leading to an undefined node" $ IntMap.lookup n imap

-- | This function takes a term, and returns a 'Dag' with the
-- implicit sharing of the input data structure made explicit.
reifyDag :: Traversable f => Tree f -> IO (Dag f)
reifyDag m = do (root, state) <- runStateT (findNodes m) init
                return (Dag root (rsEqs state) (rsNext state))
    where  init = ReifyState
                  { rsStable = HashMap.empty
                  , rsEqs = IntMap.empty
                  , rsNext = 0 }

data ReifyState f = ReifyState
    { rsStable :: HashMap (StableName (f (Tree f))) Node
    , rsEqs    :: IntMap (f Node)
    , rsNext   :: Node
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



instance (Show (f String), Functor f) => Show (Dag f)
  where
    show (Dag r es _) = unwords
        [ "mkDag"
        , show r
        , showLst ["(" ++ show n ++ "," ++ show (fmap show f) ++ ")" | (n,f) <- IntMap.toList es ]
        ]
      where
        showLst ss = "[" ++ intercalate "," ss ++ "]"

-- | Construct a dag
mkDag :: Node -> [(Node, f Node)] -> Dag f
mkDag r es = Dag r (IntMap.fromList es) (maximum (map fst es) + 1)

-- | Lift an 'IntMap.IntMap' operation to a 'Dag'. Assumes that the function does not affect the
-- set of keys.
liftDag :: (Node -> IntMap (f Node) -> IntMap (g Node)) -> Dag f -> Dag g
liftDag f (Dag r es nx) = Dag r (f r es) nx

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

-- | Removes orphan nodes from a dag
removeOrphans :: Foldable f => Node -> IntMap (f Node) -> IntMap (f Node)
removeOrphans r es = IntMap.fromSet (es IntMap.!) rs
  where
    rs = reachable r es

-- | Make an equivalent dag using consecutive indexes form 0 and up
reindexDag :: Functor f => Dag f -> Dag f
reindexDag (Dag r es _) = Dag (reix r) es' nx'
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

removeIndirections :: Functor f => Dag (Indirect f) -> Dag f
removeIndirections (Dag r es nx) = Dag (chase es r) es' nx
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

-- | Joining a dag of contexts. The node identifiers in the resulting dag are unrelated to those
-- in the original dag.
appCxtDag :: Traversable f => Dag (Free f) -> Dag f
appCxtDag g = removeIndirections $ Dag r (IntMap.fromList es') nx'
  where
    Dag r es nx = reindexDag g
    (es',nx')     = flip runState nx
                  $ execWriterT
                  $ Traversable.mapM (uncurry listCxtTop)
                  $ IntMap.assocs
                  $ es

mapDagM :: Monad m => (Node -> f Node -> m (g Node)) -> Dag f -> m (Dag g)
mapDagM f g = do
    es <- Traversable.sequence $ IntMap.mapWithKey f $ edges g
    return g {edges = es}

fromListEither :: (a -> a -> a) -> (b -> b -> b) -> [(Int, Either a b)] -> IntMap (a,b)
fromListEither fa fb as = IntMap.fromList [(i,(am IntMap.! i, bm IntMap.! i)) | i <- is]
  where
    is = IntMap.keys $ IntMap.fromList as
    am = IntMap.fromListWith fa [(i,a) | (i, Left a)  <- as]
    bm = IntMap.fromListWith fb [(i,b) | (i, Right b) <- as]


runRewriteDag :: forall f g u d . (Traversable f, Functor g, Traversable g)
    => (d -> d -> d)       -- ^ Resolution of downwards state
    -> Syn'    f (u, d) u  -- ^ Bottom-up state propagation
    -> Inh'    f (u, d) d  -- ^ Top-down state propagation
    -> Rewrite f (u, d) g  -- ^ Homomorphic rewrite
    -> (u -> d)            -- ^ Initial top-down state
    -> Dag f             -- ^ Original term
    -> (u, Dag g)        -- ^ Final state and rewritten term
runRewriteDag res up down rew dinit g = (uFin,appCxtDag gg) where
    dFin    = dinit uFin
    uFin    = fst $ env $ root g
    (gg,ws) = runWriter $ mapDagM rewNode g
    ws'     = (root g, Right dFin) : ws
    env n   = fromListEither errUp res ws' IntMap.! n
    errUp   = error "runRewriteDag1: over-constrained bottom-up state"

    rewNode :: Node -> f Node -> Writer [(Node, Either u d)] (Free g Node)
    rewNode n f = do
        tell [(n, Left (up f))]
        let dm = down f
        Traversable.forM f $ \n -> tell [(n, Right (IntMap.findWithDefault (snd ?above) n dm))]
        return (rew f)
      where
        ?above = env n
        ?below = env


-- | Run a bottom-up state automaton over a graph, resulting in a map containing the up state for
-- each node. The global environment must be defined for all nodes in the graph.
runSynDag
    :: Syn' f (u,d) u  -- Bottom-up state propagation
    -> (Node -> (u,d))     -- Global environment containing the state of each node
    -> Dag f
    -> IntMap u
runSynDag up env = IntMap.mapWithKey (\n -> explicit up (env n) env) . edges

-- | Run a top-down state automaton over a graph, resulting in a map containing the down state for
-- each node. The global environment must be defined for all nodes in the graph.
runInhDag :: forall f u d . Traversable f
    => (d -> d -> d)         -- Resolution of top-down state
    -> Inh' f (u,d) d  -- Top-down state propagation
    -> d                     -- Initial top-down state
    -> (Node -> (u,d))       -- Global environment containing the state of each node
    -> Dag f
    -> IntMap d
runInhDag res down d env g = IntMap.fromListWith res
    $ ((root g, d):)
    $ concatMap (uncurry downNode)
    $ IntMap.toList
    $ fmap number
    $ edges g
  where
    downNode :: (Functor f, Foldable f) => Node -> f (Numbered Node) -> [(Node,d)]
    downNode n f = Foldable.toList $ fmap (\(Numbered i a) -> (a, lookupNumMap (snd $ env n) i dm)) f
      where
        dm = explicit down (env n) (env . unNumbered) f

-- | Run a bidirectional state automaton over a term graph
runAGDag :: Traversable f
    => (d -> d -> d)   -- ^ Resolution of top-down state
    -> Syn' f (u,d) u  -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d  -- ^ Top-down state propagation
    -> (u -> d)        -- ^ Initial top-down state
    -> Dag f
    -> u
runAGDag res up down dinit g = uFin where
    uFin  = envU IntMap.! root g
    dFin  = dinit uFin
    envU  = runSynDag up env g
    envD  = runInhDag res down dFin env g
    env n = (envU IntMap.! n, envD IntMap.! n)



-- | This is an alternative implementation of 'runAGDag' that uses
-- mutable vectors for caching intermediate values.
runAGDagST :: forall f d u .Traversable f
    => (d -> d -> d)   -- ^ Resolution of top-down state
    -> Syn' f (u,d) u  -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d  -- ^ Top-down state propagation
    -> (u -> d)        -- ^ Initial top-down state
    -> Dag f
    -> u
runAGDagST res syn inh dinit g = uFin
    where syn' :: SynExpl f (u,d) u
          syn' = explicit syn
          inh' :: InhExpl f (u,d) d
          inh' = explicit inh
          dFin = dinit uFin
          uFin = runST runM
          runM :: ST s u
          runM = mdo dmap <- MVec.new (nodeCount g)
                     MVec.set dmap Nothing
                     MVec.unsafeWrite dmap (root g) (Just dFin)
                     umap <- MVec.new (nodeCount g)
                     count <- newSTRef 0
                     let iter (n, t) = runDownST res  syn' inh' umap dmap n
                                       (fromJust $ dmapFin Vec.! n) umapFin count t
                     mapM_ iter (IntMap.toList $ edges g)
                     dmapFin <- Vec.unsafeFreeze dmap
                     umapFin <- Vec.unsafeFreeze umap
                     return (umapFin Vec.! root g)


-- | Auxiliary function for 'runAGDagST'.
runDownST :: forall f u d s . Traversable f => (d -> d -> d) -> SynExpl f (u,d) u -> InhExpl f (u,d) d
       -> Vec.MVector s u -> Vec.MVector s (Maybe d) -> Node
     -> d -> Vec.Vector u -> STRef s Int -> f Node -> ST s ()
runDownST res syn inh ref' ref n d umap count t =
               mdo let u = syn (u,d) unNumbered result
                   let m = inh (u,d) unNumbered result

                   writeSTRef count 0
                   let run' s = do
                                   i <- readSTRef count
                                   let j = i+1
                                   writeSTRef count j
                                   let d' = lookupNumMap d i m
                                       u' = umap Vec.! s
                                   old <- MVec.unsafeRead ref s
                                   let new = case old of
                                               Just o -> res o d'
                                               _      -> d'
                                   MVec.unsafeWrite ref s (Just new)
                                   return (Numbered i (u',d'))
                   result <- Traversable.mapM run' t
                   MVec.unsafeWrite ref' n u
                   return ()


runRewriteDagST :: forall f g d u .(Traversable f, Traversable g)
    => (d -> d -> d)       -- ^ Resolution of top-down state
    -> Syn' f (u,d) u      -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d      -- ^ Top-down state propagation
    -> Rewrite f (u, d) g  -- ^ Homomorphic rewrite
    -> (u -> d)            -- ^ Initial top-down state
    -> Dag f
    -> (u, Dag g)
runRewriteDagST res syn inh rewr dinit Dag {edges=eqs,root=root,nodeCount=next} = result where
    result@(uFin,_) = runST runM
    dFin = dinit uFin
    runM :: forall s . ST s (u, Dag g)
    runM = mdo
      dmap <- MVec.new next
      MVec.set dmap Nothing
      MVec.unsafeWrite dmap root (Just dFin)
      umap <- MVec.new next
      count <- newSTRef 0
      allEqs <- MVec.new next
      let iter (node,s) = do
             let d = fromJust $ dmapFin Vec.! node
             (u,t) <- run d s
             MVec.unsafeWrite umap node u
             MVec.unsafeWrite allEqs node t
          run :: d -> f Node -> ST s (u, Free g Node)
          run d t = mdo
             let u = explicit syn (u,d) (fst . unNumbered) result
                 m = explicit inh (u,d) (fst . unNumbered) result
                 run' :: Node -> ST s (Numbered ((u,d), Node))
                 run' s = do i <- readSTRef count
                             writeSTRef count $! (i+1)
                             let d' = lookupNumMap d i m
                                 u' = umapFin Vec.! s
                             old <- MVec.unsafeRead dmap s
                             let new = case old of
                                         Just o -> res o d'
                                         _      -> d'
                             MVec.unsafeWrite dmap s (Just new)
                             return (Numbered i ((u',d'),s))
             writeSTRef count 0
             result <- Traversable.mapM run' t
             let t' = fmap (snd . unNumbered) $ explicit rewr (u,d) (fst . unNumbered) result
             return (u, t')
      mapM_ iter $ IntMap.toList eqs
      dmapFin <- Vec.unsafeFreeze dmap
      umapFin <- Vec.unsafeFreeze umap
      allEqsFin <- Vec.unsafeFreeze allEqs
      nodeCount <- newSTRef 0
      eqsref <- newSTRef IntMap.empty  -- the new graph
      newNodes :: Vec.MVector s (Maybe Int) <- MVec.new next
      MVec.set newNodes Nothing

      let build node = do
             mnewNode <- MVec.unsafeRead newNodes node
             case mnewNode of
               Just newNode -> return newNode
               Nothing -> do
                   newNode <- flatten (allEqsFin Vec.! node)
                   MVec.unsafeWrite newNodes node (Just newNode)
                   return newNode
          flatten (Ret n) = do
                       newNode <- build n
                       return newNode
          flatten (In f) = do
                       newNode <- readSTRef nodeCount
                       writeSTRef nodeCount $! (newNode+1)
                       f' <- Traversable.mapM flatten f
                       modifySTRef eqsref (IntMap.insert newNode f')
                       return newNode
      root' <- build root
      eqs' <- readSTRef eqsref
      next' <- readSTRef nodeCount
      return (umapFin Vec.! root, Dag {edges = eqs', root = root', nodeCount = next'})
