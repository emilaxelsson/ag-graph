{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecursiveDo         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleInstances   #-}


--------------------------------------------------------------------------------
-- |
-- Module      :  Dag.PAG
-- Copyright   :  (c) 2014 Patrick Bahr, Emil Axelsson
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements the recursion schemes from module
-- "PAG" on 'Dag's. In order to deal with the sharing present
-- in 'Dag's, the recursion schemes additionally take an argument of
-- type @d -> d -> d@ that resolves clashing inherited attribute
-- values.
--
--------------------------------------------------------------------------------


module Dag.PAG
    ( runPAGDag
    , module I
    ) where

import Control.Monad.ST

import Dag as I
import Dag.Internal
import Mapping as I
import PAG.Projection as I
import PAG.Internal
import qualified PAG.Internal as I hiding (explicit)
import Tree as I

import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)

import Data.Vector (MVector)


import Data.Maybe
import Data.STRef
import qualified Data.Traversable as Traversable


import qualified Data.Vector as Vec
import qualified Data.Vector.Generic.Mutable as MVec

import Control.Monad.State


-- | This function runs an attribute grammar on a dag. The result is
-- the (combined) synthesised attribute at the root of the dag.

runPAGDag :: forall f d u g . (Traversable f, Traversable d, Traversable g, Traversable u)
      => (forall a . d a -> d a -> d a)      -- ^ resolution function for inherited attributes
      -> Syn' f (u :*: d) u g                -- ^ semantic function of synthesised attributes
      -> Inh' f (u :*: d) d g                -- ^ semantic function of inherited attributes
      -> (forall a . u a -> d (Free g a)) -- ^ initialisation of inherited attributes
      -> Dag f                               -- ^ input term
      -> u (Dag g)
runPAGDag res syn inh dinit Dag {edges,root,nodeCount} = result where
    (uFin, result) = runST runM
    runM :: forall s . ST s (u Node, u (Dag g))
    runM = mdo
      -- construct empty mapping from nodes to inherited attribute values
      dmap <- MVec.new nodeCount
      MVec.set dmap Nothing
      -- allocate mapping from nodes to synthesised attribute values
      umap <- MVec.new nodeCount
      -- allocate counter for numbering child nodes
      count <- newSTRef 0
      -- allocate references represent edges of the target DAG
      nextNode <- newSTRef 0
      newEdges <- newSTRef (IntMap.empty :: IntMap (g (Free g Node)))
      let -- This function is applied to each edge
          iter (node,s) = do
             writeSTRef count 0
             let d = fromJust $ dmapFin Vec.! node
             u <- run d s
             MVec.unsafeWrite umap node u
          -- Runs the AG on an edge with the given input inherited
          -- attribute value and produces the output synthesised
          -- attribute value along with the rewritten subtree.
          run :: d Node -> f (Free f Node) -> ST s (u Node)
          run d t = mdo
             e <- readSTRef newEdges
             n <- readSTRef nextNode
             -- apply the semantic functions
             let mkFresh = liftM2 (,) (Traversable.mapM freshNode $  explicit syn (u :*: d) unNumbered result)
                                      (Traversable.mapM (Traversable.mapM freshNode) $  explicit inh (u :*: d) unNumbered result)
                 ((u,m),(Fresh n' e')) = runState mkFresh (Fresh n e)
             writeSTRef newEdges e'
             writeSTRef nextNode n'
                 -- recurses into the child nodes and numbers them
             let run' :: Free f Node -> ST s (Numbered ((u :*: d) Node))
                 run' s = do i <- readSTRef count
                             writeSTRef count $! (i+1)
                             let d' = case lookupNumMap' i m of
                                       Nothing -> d
                                       Just d' -> d'
                             u' <- runF d' s
                             return (Numbered i (u' :*: d'))
             result <- Traversable.mapM run' t
             return u
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
             return (umapFin Vec.! x)
      e <- readSTRef newEdges
      n <- readSTRef nextNode
      let (dFin,Fresh n' e') = runState (Traversable.mapM freshNode $ dinit uFin) (Fresh n e)
      writeSTRef newEdges e'
      writeSTRef nextNode n'
      -- first apply to the root
      u <- run dFin root
      -- then apply to the edges
      mapM_ iter $ IntMap.toList edges
      -- finalise the mappings for attribute values and target DAG
      dmapFin <- Vec.unsafeFreeze dmap
      umapFin <- Vec.unsafeFreeze umap
      newEdgesFin <- readSTRef newEdges
      newEdgesCount <- readSTRef nextNode
      let relabel n = relabelNodes n newEdgesFin newEdgesCount
      return (u, fmap relabel u)


-- | The state space for the function 'freshNode'.

data Fresh f = Fresh {nextFreshNode :: Int, freshEdges :: IntMap (f (Free f Node))}

-- | Allocates a fresh node for the given context. A new edge is store
-- in the state monad that maps the fresh node to the context that was
-- passed to the function. If the context is just a single node, that
-- node is returned.

freshNode :: Free g Node -> State (Fresh g) Node
freshNode (Ret n) = return n
freshNode (In t) = do
  s <- get
  let n = nextFreshNode s
      e = freshEdges s
  put (s {freshEdges= IntMap.insert n t e, nextFreshNode = n+1 })
  return n


-- | This function relabels the nodes of the given dag. Parts that are
-- unreachable from the root are discarded.
relabelNodes :: forall f . Traversable f
             => Node
             -> IntMap (f (Free f Node))
             -> Int
             -> Dag f
relabelNodes root edges nodeCount = runST run where
    run :: ST s (Dag f)
    run = do
      -- allocate counter for generating nodes
      curNode <- newSTRef 0
      newEdges <- newSTRef IntMap.empty  -- the new graph
      -- construct empty mapping for mapping old nodes to new nodes
      newNodes :: MVector s (Maybe Int) <- MVec.new nodeCount
      MVec.set newNodes Nothing
      let -- Replaces node in the old graph with a node in the new
          -- graph. This function is applied to all nodes reachable
          -- from the given node as well.
          build :: Node -> ST s Node
          build node = do
            -- check whether we have already constructed a new node
            -- for the given node
             mnewNode <- MVec.unsafeRead newNodes node
             case mnewNode of
               Just newNode -> return newNode
               Nothing -> do
                        -- Create a new node and call build recursively
                       newNode <- readSTRef curNode
                       writeSTRef curNode $! (newNode+1)
                       MVec.unsafeWrite newNodes node (Just newNode)
                       f' <- Traversable.mapM (Traversable.mapM build) (edges IntMap.! node)
                       modifySTRef newEdges (IntMap.insert newNode f')
                       return newNode
      -- start relabelling from the root
      root' <- Traversable.mapM (Traversable.mapM build) (edges IntMap.! root)
      -- collect the final edges mapping and node count
      edges' <- readSTRef newEdges
      nodeCount' <- readSTRef curNode
      return Dag {edges = edges', root = root', nodeCount = nodeCount'}
