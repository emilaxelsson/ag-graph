{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

-- This is an implementation of repmin as a PAG. The use of a PAG
-- allows us to implement repmin such that the result of repmin is a
-- DAG with only one leaf node, which is shared throughout the
-- DAG. This is achieved as follows instead of only collecting the
-- minimum synthesised attribute and then turning it into an inherited
-- attribute, which propagates the minimum to the leaves of the graph,
-- we construct a single leaf node with the minimum labelling and
-- propagate it downwards as an inherited attribute.

module RepminPAG where

import Paper (IntTreeF(..))
import PAG
import Dag.PAG

import Data.Foldable
import System.IO.Unsafe

newtype MinS a = MinS {unMinS :: Int} deriving (Functor, Foldable, Traversable)
newtype MinI a = MinI a deriving (Functor, Foldable, Traversable)

data I a = I {unI :: a} deriving (Functor, Foldable, Traversable)

iNode x y = In (Node x y)
iLeaf i = In (Leaf i)


minS ::  Syn IntTreeF atts MinS f
minS (Leaf i)    =  MinS i
minS (Node a b)  =  MinS $ min (unMinS $ below a) (unMinS $ below b)

minI :: Inh IntTreeF atts MinI f
minI _ = empty


globMin  ::  (?above :: atts n, MinI :< atts) => n
globMin  =   let MinI i = above in i


rep ::  (MinI :< atts) => Syn IntTreeF atts I IntTreeF
rep (Leaf _)    =  I (Ret globMin)
rep (Node a b)  =  I $ iNode (Ret $ unI $ below a) (Ret $ unI $ below b)


repminG :: Dag IntTreeF -> Dag IntTreeF
repminG = unI . ffst . runPAGDag const (rep |*| minS) minI  init
  where init (_ :*: MinS i) = MinI (iLeaf i)


repmin :: Tree IntTreeF -> Tree IntTreeF
repmin = unI . ffst . runPAG (rep |*| minS) minI  init
  where init (_ :*: MinS i) = MinI (iLeaf i)


it1 :: Tree IntTreeF
it1 = iNode (iNode x (iLeaf 10)) x
    where x = iNode y y
          y = iLeaf 20

i1 :: Dag IntTreeF
i1 = unsafePerformIO $ reifyDag it1


it2 :: Tree IntTreeF
it2 = iNode x (iNode (iLeaf 5) x)
    where x = iNode (iNode (iLeaf 24) (iLeaf 3)) (iLeaf 4)

i2 :: Dag IntTreeF
i2 = unsafePerformIO $ reifyDag it2
