{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecursiveDo         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE DeriveFunctor       #-}


--------------------------------------------------------------------------------
-- |
-- Module      :  Dag.AG
-- Copyright   :  (c) 2014 Patrick Bahr, Emil Axelsson
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements the recursion schemes from module
-- "AG" on 'Dag's. In order to deal with the sharing present
-- in 'Dag's, the recursion schemes additionally take an argument of
-- type @d -> d -> d@ that resolves clashing inherited attribute
-- values.
--
--------------------------------------------------------------------------------


module DagSimple.AG
    ( runAGDag
    , runRewriteDag
    , module I
    ) where

import Control.Monad.ST
import Control.Monad.State
import AG.Internal
import qualified AG.Internal as I hiding (explicit)
import DagSimple as I
import DagSimple.Internal
import Mapping as I
import Projection as I
import Tree as I
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Data.Maybe
import Data.STRef
import qualified Data.Traversable as Traversable
import Data.Vector (Vector,MVector)
import qualified Data.Vector as Vec
import Data.Vector ((!))
import qualified Data.Vector.Generic.Mutable as MVec
import Control.Monad.Writer


-- | This function runs an attribute grammar on a dag. The result is
-- the (combined) synthesised attribute at the root of the dag.

runAGDag :: forall f i s .Traversable f
    => (i -> i -> i)   -- ^ resolution function for inherited attributes
    -> Syn' f (s,i) s  -- ^ semantic function of synthesised attributes
    -> Inh' f (s,i) i  -- ^ semantic function of inherited attributes
    -> (s -> i)        -- ^ initialisation of inherited attributes
    -> Dag f           -- ^ input dag
    -> s
runAGDag res syn inh iinit Dag {edges,root,nodeCount} = sFin where
    sFin = runST runM
    iFin = iinit sFin
    runM :: forall st . ST st s
    runM = mdo
      -- construct empty mapping from nodes to inherited attribute values
      imap <- MVec.new nodeCount
      MVec.set imap Nothing
      -- allocate mapping from nodes to synthesised attribute values
      smap <- MVec.new nodeCount
      -- allocate counter for numbering child nodes
      count <- newSTRef 0
      let -- Runs the AG on an edge with the given input inherited
          -- attribute value and produces the output synthesised
          -- attribute value.
          run :: i -> f Node -> ST st s
          run i t = mdo
             -- apply the semantic functions
             let s = explicit syn (s,i) unNumbered result
                 m = explicit inh (s,i) unNumbered result
                 -- recurses into the child nodes and numbers them
                 run' :: Node -> ST st (Numbered (s,i))
                 run' c = do n <- readSTRef count
                             writeSTRef count $! (n+1)
                             let i' = lookupNumMap i n m
                             s' <- runF i' c -- recurse
                             return (Numbered n (s',i'))
             result <- Traversable.mapM run' t
             return s
          runF :: i -> Node -> ST st s
          runF i x = do
             -- we found a node: update the mapping for inherited
             -- attribute values
             old <- MVec.unsafeRead imap x
             let new = case old of
                         Just o -> res o i
                         _      -> i
             MVec.unsafeWrite imap x (Just new)
             return (smapFin ! x)
          -- This function is applied to each edge
          iter (n, t) = do
            writeSTRef count 0  -- re-initialize counter
            s <- run (fromJust $ imapFin ! n) t
            MVec.unsafeWrite smap n s
      -- first apply to the root
      s <- runF iFin root
      -- then apply to the edges
      mapM_ iter (IntMap.toList edges)
      -- finalise the mappings for attribute values
      imapFin <- Vec.unsafeFreeze imap
      smapFin <- Vec.unsafeFreeze smap
      return s



-- | This function runs an attribute grammar with rewrite function on
-- a dag. The result is the (combined) synthesised attribute at the
-- root of the dag and the rewritten dag.

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
        let f' = number f
        tell [(n, Left (up f'))]
        let dm = down f'
        Traversable.forM f' $ \(Numbered n _) -> tell [(n, Right (lookupNumMap (snd ?above) n dm))]
        return $ fmap unNumbered (rew f')
      where
        ?above = env n
        ?below = env . unNumbered


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


removeIndirections :: Functor f => Dag (Indirect f) -> Dag f
removeIndirections (Dag r es nx) = Dag (chase es r) es' nx
  where
    es' = IntMap.mapMaybe direct $ fmap (fmap (chase es)) es


-- | Make an equivalent dag using consecutive indexes form 0 and up
reindexDag :: Functor f => Dag f -> Dag f
reindexDag (Dag r es _) = Dag (reix r) es' nx'
  where
    (ns,fs) = unzip $ IntMap.toList es
    reix    = (IntMap.!) (IntMap.fromList (zip ns [0..]))
    es'     = IntMap.fromAscList $ zip [0..] $ map (fmap reix) fs
    nx'     = length ns

-- | Turn a 'Free' into an association list where the provided node @n@ maps to the root of the
-- context
listCxtTop :: Traversable f =>
    Node -> Free f Node -> WriterT [(Node, Indirect f Node)] (State Node) ()
listCxtTop n (Ret n') = tell [(n, Indirect n')]
listCxtTop n (In f)  = do
    (f',es) <- lift $ runWriterT $ Traversable.mapM listCxt f
    tell [(n, Direct f')]
    tell $ map (\(n,f) -> (n, Direct f)) es



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

-- | Turn a 'Free' into an association list each node has a freshly generated identifier
listCxt :: Traversable f => Free f Node -> WriterT [(Node, f Node)] (State Node) Node
listCxt (Ret n) = return n
listCxt (In f) = do
    n  <- freshNode
    f' <- Traversable.mapM listCxt f
    tell [(n,f')]
    return n


freshNode :: MonadState Node m => m Node
freshNode = do
    n <- get
    put (succ n)
    return n
