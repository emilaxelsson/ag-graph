{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecursiveDo         #-}
{-# LANGUAGE ScopedTypeVariables #-}


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


module Dag.AG
    ( runAGDag
    , runRewriteDag
    , module I
    ) where

import Control.Monad.ST
import Control.Monad.State
import AG.Internal
import qualified AG.Internal as I hiding (explicit)
import Dag as I
import Dag.Internal
import Mapping as I
import Projection as I
import Tree as I
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.STRef
import qualified Data.Traversable as Traversable
import Data.Vector (Vector,MVector)
import qualified Data.Vector as Vec
import Data.Vector ((!))
import qualified Data.Vector.Generic.Mutable as MVec

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
          run :: i -> f (Free f Node) -> ST st s
          run i t = mdo
             -- apply the semantic functions
             let s = explicit syn (s,i) unNumbered result
                 m = explicit inh (s,i) unNumbered result
                 -- recurses into the child nodes and numbers them
                 run' :: Free f Node -> ST st (Numbered (s,i))
                 run' c = do n <- readSTRef count
                             writeSTRef count $! (n+1)
                             let i' = lookupNumMap i n m
                             s' <- runF i' c -- recurse
                             return (Numbered n (s',i'))
             result <- Traversable.mapM run' t
             return s
          -- recurses through the tree structure
          runF :: i -> Free f Node -> ST st s
          runF i (Ret x) = do
             -- we found a node: update the mapping for inherited
             -- attribute values
             old <- MVec.unsafeRead imap x
             let new = case old of
                         Just o -> res o i
                         _      -> i
             MVec.unsafeWrite imap x (Just new)
             return (smapFin ! x)
          runF i (In t)  = run i t
          -- This function is applied to each edge
          iter (n, t) = do
            writeSTRef count 0  -- re-initialize counter
            s <- run (fromJust $ imapFin ! n) t
            MVec.unsafeWrite smap n s
      -- first apply to the root
      s <- run iFin root
      -- then apply to the edges
      mapM_ iter (IntMap.toList edges)
      -- finalise the mappings for attribute values
      imapFin <- Vec.unsafeFreeze imap
      smapFin <- Vec.unsafeFreeze smap
      return s



-- | This function runs an attribute grammar with rewrite function on
-- a dag. The result is the (combined) synthesised attribute at the
-- root of the dag and the rewritten dag.

runRewriteDag :: forall f g d u .(Traversable f, Traversable g)
    => (d -> d -> d)       -- ^ resolution function for inherited attributes
    -> Syn' f (u,d) u      -- ^ semantic function of synthesised attributes
    -> Inh' f (u,d) d      -- ^ semantic function of inherited attributes
    -> Rewrite f (u, d) g  -- ^ initialisation of inherited attributes
    -> (u -> d)            -- ^ input term
    -> Dag f
    -> (u, Dag g)
runRewriteDag res syn inh rewr dinit Dag {edges,root,nodeCount} = result where
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
             writeSTRef count 0
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
