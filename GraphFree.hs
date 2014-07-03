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

import qualified Data.Map as Map
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
    => (d -> d -> d)         -- ^ Resolution of top-down state
    -> Syn' f (u,d) u  -- ^ Bottom-up state propagation
    -> Inh' f (u,d) d  -- ^ Top-down state propagation
    -> d                     -- ^ Initial top-down state
    -> Graph f
    -> u
runAGGraph res syn inh d g = umap IntMap.! _root g
    where syn' :: SynExpl f (u,d) u
          syn' = explicit syn
          inh' :: InhExpl f (u,d) d
          inh' = explicit inh
          run = free res  syn' inh'
          dmap = IntMap.foldr (\ (_,m1) m2 -> IntMap.unionWith res m1 m2) 
                 (IntMap.singleton (_root g) d) result
          umap = IntMap.map fst result
          result = IntMap.mapWithKey (\ n t -> run (dmap IntMap.! n) umap t) (_eqs g)


-- | Auxiliary function for 'runAGGraph'.

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

-- | Alternative implementation of 'runAGGraph' that uses mutable
-- vectors for caching intermediate values.

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
                     MVec.unsafeWrite dmap (_root g) (Just d)
                     umap <- MVec.new (_next g)
                     let iter (n, t) = do 
                           u <- freeST res  syn' inh' dmap (fromJust $ dmapFin Vec.! n) umapFin t   
                           MVec.unsafeWrite umap n u
                           return ()
                     mapM_ iter (IntMap.toList $ _eqs g)
                     dmapFin <- Vec.unsafeFreeze dmap
                     umapFin <- Vec.unsafeFreeze umap
                     return (umapFin Vec.! _root g)



-- | Auxiliary function for 'runAGGraphST'.

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


termTree :: Functor f => Tree f -> Graph f
termTree t = Simple.Graph 0 (IntMap.singleton 0 (freeTree t)) 1
