{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DoAndIfThenElse     #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}


--------------------------------------------------------------------------------
-- |
-- Module      :  Dag
-- Copyright   :  (c) 2014 Patrick Bahr, Emil Axelsson
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements a representation of directed acyclic graphs
-- (DAGs) as compact representations of trees (or 'Tree's).
--
--------------------------------------------------------------------------------

module Dag
    ( Dag
    , termTree
    , reifyDag
    , unravelDag
    , bisim
    , iso
    , strongIso
    , flatten
    ) where

import Control.Applicative
import Control.Exception.Base
import Control.Monad.State
import Dag.Internal
import Tree
import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable (toList)
import qualified Data.HashMap.Lazy as HashMap
import Data.IntMap
import qualified Data.IntMap as IntMap
import Data.IORef
import Data.Traversable (Traversable)
import qualified Data.Traversable as Traversable
import Data.Typeable
import System.Mem.StableName

import Control.Monad.ST

import Data.List
import Data.STRef
import qualified Data.Vector as Vec
import qualified Data.Vector.Generic.Mutable as MVec



eqF :: (Eq (f ()), Functor f) => f a -> f b -> Bool
eqF s t = (() <$ s) == (() <$ t)

 {-| This function implements equality of values of type @f a@ modulo
the equality of @a@ itself. If two functorial values are equal in this
sense, 'eqMod' returns a 'Just' value containing a list of pairs
consisting of corresponding components of the two functorial
values. -}
eqMod :: (Eq (f ()), Functor f, Foldable f) => f a -> f b -> Maybe [(a,b)]
eqMod s t
    | s `eqF` t = Just args
    | otherwise = Nothing
    where args = Foldable.toList s `zip` Foldable.toList t


instance (Show (f NewString), Functor f) => Show (Dag f)
  where
    show (Dag r es _) = unwords
        [ "mkDag"
        , show  (In r)
        , showLst ["(" ++ show n ++ "," ++ show (In f) ++ ")" | (n,f) <- IntMap.toList es ]
        ]
      where
        showLst ss = "[" ++ intercalate "," ss ++ "]"



-- | Turn a term into a graph without sharing.
termTree :: Functor f => Tree f -> Dag f
termTree (In t) = Dag (fmap freeTree t) IntMap.empty 0

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


-- | This function unravels a given graph to the term it
-- represents.

unravelDag :: forall f. Functor f => Dag f -> Tree f
unravelDag Dag {edges, root} = In $ build <$> root
    where build :: Free f Node -> Tree f
          build (In t) = In $ build <$> t
          build (Ret n) = In $ build <$> edges IntMap.! n

-- | Checks whether two dags are bisimilar. In particular, we have
-- the following equality
--
-- @
-- bisim g1 g2 = (unravel g1 == unravel g2)
-- @
--
-- That is, two dags are bisimilar iff they have the same unravelling.

bisim :: forall f . (Eq (f ()), Functor f, Foldable f)  => Dag f -> Dag f -> Bool
bisim Dag {root=r1,edges=e1}  Dag {root=r2,edges=e2} = runF r1 r2
    where run :: (Free f Node, Free f Node) -> Bool
          run (t1, t2) = runF (step e1 t1) (step e2 t2)
          step :: Edges f -> Free f Node -> f (Free f Node)
          step e (Ret n) = e IntMap.! n
          step _ (In t) = t
          runF :: f (Free f Node) -> f (Free f Node) -> Bool
          runF f1 f2 = case eqMod f1 f2 of
                         Nothing -> False
                         Just l -> all run l


-- | Checks whether the two given DAGs are isomorphic.

iso :: (Traversable f, Foldable f, Eq (f ())) => Dag f -> Dag f -> Bool
iso g1 g2 = checkIso eqMod (flatten g1) (flatten g2)


-- | Checks whether the two given DAGs are strongly isomorphic, i.e.
--   their internal representation is the same modulo renaming of
--   nodes.

strongIso :: (Functor f, Foldable f, Eq (f (Free f ()))) => Dag f -> Dag f -> Bool
strongIso Dag {root=r1,edges=e1,nodeCount=nx1}
          Dag {root=r2,edges=e2,nodeCount=nx2}
              = checkIso checkEq (r1,e1,nx1) (r2,e2,nx2)
    where checkEq t1 t2 = eqMod (In t1) (In t2)



-- | This function flattens the internal representation of a DAG. That
-- is, it turns the nested representation of edges into single layers.

flatten :: forall f . Traversable f => Dag f -> (f Node, IntMap (f Node), Int)
flatten Dag {root,edges,nodeCount} = runST run where
    run :: forall s . ST s (f Node, IntMap (f Node), Int)
    run = do
      count <- newSTRef 0
      nMap :: Vec.MVector s (Maybe Node) <- MVec.new nodeCount
      MVec.set nMap Nothing
      newEdges <- newSTRef IntMap.empty
      let build :: Free f Node -> ST s Node
          build (Ret n) = mkNode n
          build (In t) = do
            n' <- readSTRef count
            writeSTRef count $! (n'+1)
            t' <- Traversable.mapM build t
            modifySTRef newEdges (IntMap.insert n' t')
            return n'
          mkNode n = do
            mn' <- MVec.unsafeRead nMap n
            case mn' of
              Just n' -> return n'
              Nothing -> do n' <- readSTRef count
                            writeSTRef count $! (n'+1)
                            MVec.unsafeWrite nMap n (Just n')
                            return n'
          buildF (n,t) = do
            n' <- mkNode n
            t' <- Traversable.mapM build t
            modifySTRef newEdges (IntMap.insert n' t')
      root' <- Traversable.mapM build root
      mapM_ buildF $ IntMap.toList edges
      edges' <- readSTRef newEdges
      nodeCount' <- readSTRef count
      return (root', edges', nodeCount')



-- | Checks whether the two given dag representations are
-- isomorphic. This function is polymorphic in the representation of
-- the edges. The first argument is a function that checks whether two
-- edges have the same labelling and if so, returns the matching pairs
-- of outgoing nodes the two edges point to. Otherwise the function
-- returns 'Nothing'.

checkIso :: (e -> e -> Maybe [(Node,Node)])
         -> (e, IntMap e, Int)
         -> (e, IntMap e, Int) -> Bool
checkIso checkEq (r1,e1,nx1) (r2,e2,nx2) = runST run where
   run :: ST s Bool
   run = do
     -- create empty mapping from nodes in g1 to nodes in g2
     nMap :: Vec.MVector s (Maybe Node) <- MVec.new nx1
     MVec.set nMap Nothing
     -- create empty set of nodes in g2 that are "mapped to" by the
     -- mapping created above
     nSet :: Vec.MVector s Bool <- MVec.new nx2
     MVec.set nSet False
     let checkT t1 t2 = case checkEq t1 t2 of
                          Nothing -> return False
                          Just l -> liftM and $ mapM checkN l
         checkN (n1,n2) = do
           nm' <- MVec.unsafeRead nMap n1
           case nm' of
             Just n' -> return (n2 == n')
             _ -> do
               b <- MVec.unsafeRead nSet n2
               if b
               -- n2 is already mapped to by another node
               then return False
               -- n2 is not mapped to
               else do
                 -- create mapping from n1 to n2
                 MVec.unsafeWrite nMap n1 (Just n2)
                 MVec.unsafeWrite nSet n2 True
                 checkT (e1 IntMap.! n1) (e2 IntMap.! n2)
     checkT r1 r2
