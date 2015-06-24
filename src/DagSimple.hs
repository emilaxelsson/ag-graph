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
-- Module      :  DagSimple
-- Copyright   :  (c) 2014 Patrick Bahr, Emil Axelsson
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements a naive representation of directed acyclic
-- graphs (DAGs) as compact representations of trees (or 'Tree's).
--
--------------------------------------------------------------------------------

module DagSimple
    ( Dag
    , termTree
    , reifyDag
    , unravelDag
    , toSimple
    ) where

import Control.Applicative
import Control.Monad.State
import DagSimple.Internal
import Tree
import qualified Dag
import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable (toList)
import qualified Data.HashMap.Lazy as HashMap
import Data.IntMap
import qualified Data.IntMap as IntMap
import Data.Traversable (Traversable)
import qualified Data.Traversable as Traversable
import System.Mem.StableName
import Control.Monad.Writer
import Data.HashMap.Lazy (HashMap)
import Data.List
import Safe


-- | Internal function used to lookup the nodes in a dag. It assumes
-- a node of a dag that is either the root node or a target node of
-- one of the edges. The implementation of this function makes use of
-- the invariant that each such node must also be in the domain of the
-- IntMap of the dag.
lookupNode :: Node -> IntMap (f Node) -> f Node
lookupNode n imap = fromJustNote "edge leading to an undefined node" $ IntMap.lookup n imap


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


instance (Show (f String), Functor f) => Show (Dag f)
  where
    show (Dag r es _) = unwords
        [ "mkDag"
        , show r
        , showLst ["(" ++ show n ++ "," ++ show (fmap show f) ++ ")" | (n,f) <- IntMap.toList es ]
        ]
      where
        showLst ss = "[" ++ intercalate "," ss ++ "]"

-- | Turn a term into a graph without sharing.
termTree :: Traversable f => Tree f -> Dag f
termTree t = Dag 0 imap nx
    where (imap,nx) = runState (liftM snd $ runWriterT $ build t) 0
          build :: Traversable f => Tree f -> WriterT (IntMap (f Node)) (State Node) Node
          build (In t) = do n <- get
                            put (n+1)
                            res <- Traversable.mapM build t
                            tell $ IntMap.singleton n res
                            return n



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

-- | This function unravels a given graph to the term it
-- represents.

unravelDag :: forall f. Functor f => Dag f -> Tree f
unravelDag g = build (root g)
    where build :: Node -> Tree f
          build n = In $ fmap build $ lookupNode n (edges g)


toSimple :: Traversable f => Dag.Dag f -> Dag f
toSimple dag = Dag count (IntMap.insert count root edges) (count + 1)
  where (root, edges, count) = Dag.flatten dag

-- | Checks whether two dags are bisimilar. In particular, we have
-- the following equality
--
-- @
-- bisim g1 g2 = (unravel g1 == unravel g2)
-- @
--
-- That is, two dags are bisimilar iff they have the same unravelling.

-- TODO implement

-- bisim :: forall f . (Eq (f ()), Functor f, Foldable f)  => Dag f -> Dag f -> Bool
-- bisim Dag {root=r1,edges=e1}  Dag {root=r2,edges=e2} = runF r1 r2
--     where run :: (Free f Node, Free f Node) -> Bool
--           run (t1, t2) = runF (step e1 t1) (step e2 t2)
--           step :: Edges f -> Free f Node -> f (Free f Node)
--           step e (Ret n) = e IntMap.! n
--           step _ (In t) = t
--           runF :: f (Free f Node) -> f (Free f Node) -> Bool
--           runF f1 f2 = case eqMod f1 f2 of
--                          Nothing -> False
--                          Just l -> all run l


-- | Checks whether the two given DAGs are isomorphic.

-- iso :: (Traversable f, Foldable f, Eq (f ())) => Dag f -> Dag f -> Bool
-- iso g1 g2 = checkIso eqMod (flatten g1) (flatten g2)


-- | Checks whether the two given DAGs are strongly isomorphic, i.e.
--   their internal representation is the same modulo renaming of
--   nodes.

-- strongIso :: (Functor f, Foldable f, Eq (f (Free f ()))) => Dag f -> Dag f -> Bool
-- strongIso Dag {root=r1,edges=e1,nodeCount=nx1}
--           Dag {root=r2,edges=e2,nodeCount=nx2}
--               = checkIso checkEq (r1,e1,nx1) (r2,e2,nx2)
--     where checkEq t1 t2 = eqMod (In t1) (In t2)
