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


-- Alternative representation of graph that combines the simple graph
-- representation from the "Graph" module with the tree
-- representation. The goal of this representation is to reduce the
-- overhead of the graph representation for graphs with little or no
-- sharing.

module GraphFree where

import qualified Graph as Simple

import Graph (Node, _root, _eqs, _next)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import qualified Data.Foldable as Foldable
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import qualified Data.Traversable as Traversable

import Control.Monad.State

import Control.Monad.ST
import Data.STRef
import qualified Data.Vector as Vec
import qualified Data.Vector.Generic.Mutable as MVec
import Data.Maybe

import AG

type Graph f = Simple.Graph (Free f)


-- | This function runs an AG on a graph.
runAGGraph :: forall f d u .Traversable f
    => (d -> d -> d)   -- ^ Resolution of top-down state
    -> Syn' f (u,d) u  -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d  -- ^ Top-down state propagation
    -> (u -> d)        -- ^ Initial top-down state
    -> Graph f
    -> u
runAGGraph res syn inh dinit g = uFin where
    uFin = umapFin IntMap.! _root g
    dFin = dinit uFin
    run :: d -> Free f Node -> (u, IntMap d)
    run d (Ret x) = (umapFin IntMap.! x, IntMap.singleton x d)
    run d (In t)  = (u, dmapLoc) where
        u = explicit syn (u,d) unNumbered result
        m = explicit inh (u,d) unNumbered result
        (result, (dmapLoc,_)) = runState (Traversable.mapM run' t) (IntMap.empty,0)
        run' :: Free f Node -> State (IntMap d, Int) (Numbered ((u,d)))
        run' s = do
            (oldDmap,i) <- get
            let d' = lookupNumMap d i m
                (u',dmap') = run d' s
            let j = i+1
            j `seq` put (IntMap.unionWith res dmap' oldDmap, j)
            return (Numbered i (u',d'))
    dmapFin = IntMap.foldr (\ (_,m1) m2 -> IntMap.unionWith res m1 m2) 
           (IntMap.singleton (_root g) dFin) result
    umapFin = IntMap.map fst result
    result = IntMap.mapWithKey (\ n t -> run (dmapFin IntMap.! n) t) (_eqs g)


-- | Alternative implementation of 'runAGGraph' that uses mutable
-- vectors for caching intermediate values.

runAGGraphST :: forall f d u .Traversable f
    => (d -> d -> d)   -- ^ Resolution of top-down state
    -> Syn' f (u,d) u  -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d  -- ^ Top-down state propagation
    -> (u -> d)        -- ^ Initial top-down state
    -> Graph f
    -> u
runAGGraphST res syn inh dinit g = uFin where
    uFin = runST runM
    dFin = dinit uFin
    runM :: forall s . ST s u
    runM = mdo
      dmap <- MVec.new (_next g)
      MVec.set dmap Nothing
      MVec.unsafeWrite dmap (_root g) (Just dFin)
      umap <- MVec.new (_next g)
      count <- newSTRef 0
      let run :: d -> Free f Node -> ST s u
          run d (Ret x) = do 
            old <- MVec.unsafeRead dmap x
            let new = case old of
                        Just o -> res o d
                        _      -> d
            MVec.unsafeWrite dmap x (Just new)
            return (umapFin Vec.! x)
          run d (In t)  = mdo 
            let u = explicit syn (u,d) unNumbered result
                m = explicit inh (u,d) unNumbered result
                run' :: Free f Node -> ST s (Numbered (u,d))
                run' s = do 
                  i <- readSTRef count
                  let j = i+1
                  j `seq` writeSTRef count j
                  let d' = lookupNumMap d i m
                  u' <- run d' s
                  return (Numbered i (u',d'))
            writeSTRef count 0
            result <- Traversable.mapM run' t
            return u
          iter (n, t) = do 
            u <- run (fromJust $ dmapFin Vec.! n) t
            MVec.unsafeWrite umap n u
      mapM_ iter (IntMap.toList $ _eqs g)
      dmapFin <- Vec.unsafeFreeze dmap
      umapFin <- Vec.unsafeFreeze umap
      return (umapFin Vec.! _root g)


runRewriteGraphST :: forall f g d u .(Traversable f, Functor g, Foldable g)
    => (d -> d -> d)       -- ^ Resolution of top-down state
    -> Syn' f (u,d) u      -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d      -- ^ Top-down state propagation
    -> Rewrite f (u, d) g  -- ^ Homomorphic rewrite
    -> (u -> d)            -- ^ Initial top-down state
    -> Graph f
    -> (u, Graph g)
runRewriteGraphST res syn inh rewr dinit g = (uFin, gFin) where
    (uFin,gFin) = runST runM
    dFin = dinit uFin
    runM :: forall s . ST s (u, Graph g)
    runM = mdo
      dmap <- MVec.new (_next g)
      MVec.set dmap Nothing
      MVec.unsafeWrite dmap (_root g) (Just dFin)
      umap <- MVec.new (_next g)
      count <- newSTRef 0
      eqsref <- newSTRef IntMap.empty
      let eqs = _eqs g
      let iter node = do neweqs <- readSTRef eqsref
                         unless (IntMap.member node neweqs) $ do
                           let s = IntMap.findWithDefault (error "runRewriteGraphST") node eqs
                               d = fromJust $ dmapFin Vec.! node
                           (u,t) <- run d s
                           MVec.unsafeWrite umap node u 
                           modifySTRef eqsref (IntMap.insert node t)
                           Foldable.mapM_ iter t
          run :: d -> Free f Node -> ST s (u, Free g Node)
          run d (Ret x) = do 
             old <- MVec.unsafeRead dmap x
             let new = case old of
                         Just o -> res o d
                         _      -> d
             MVec.unsafeWrite dmap x (Just new)
             return (umapFin Vec.! x, Ret x)
          run d (In t)  = mdo 
             let u = explicit syn (u,d) (fst . unNumbered) result
                 m = explicit inh (u,d) (fst . unNumbered) result
                 run' :: Free f Node -> ST s (Numbered ((u,d), Free g Node))
                 run' s = do i <- readSTRef count
                             let j = i+1
                             j `seq` writeSTRef count j
                             let d' = lookupNumMap d i m
                             (u',t) <- run d' s
                             return (Numbered i ((u',d'), t))
             writeSTRef count 0
             result <- Traversable.mapM run' t
             let t' = join $ fmap (snd . unNumbered) $ explicit rewr (u,d) (fst . unNumbered) result
             return (u, t')
      iter (_root g)
      dmapFin <- Vec.unsafeFreeze dmap
      umapFin <- Vec.unsafeFreeze umap
      eqs' <- readSTRef eqsref
      return (umapFin Vec.! _root g, g {_eqs = eqs'})


termTree :: Functor f => Tree f -> Graph f
termTree t = Simple.Graph 0 (IntMap.singleton 0 (freeTree t)) 1
