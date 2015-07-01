{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImplicitParams #-}

module Repmin where

import LeavesBelow (IntTreeF (..),i1,i2)

import Dag.Internal
import AG
import Dag.AG




--------------------------------------------------------------------------------
-- * Repmin
--------------------------------------------------------------------------------

newtype MinS = MinS Int deriving (Eq,Ord)
newtype MinI = MinI Int

globMin  ::  (?above :: atts, MinI :< atts) => Int
globMin  =   let MinI i = above in i

minS ::  Syn IntTreeF atts MinS
minS (Leaf i)    =  MinS i
minS (Node a b)  =  min (below a) (below b)

minI :: Inh IntTreeF atts MinI
minI _ = o

rep ::  (MinI :< atts) => Syn IntTreeF atts (Tree IntTreeF)
rep (Leaf i)    =  In (Leaf globMin)
rep (Node a b)  =  In (Node (below a) (below b))

repmin :: Tree IntTreeF -> Tree IntTreeF
repmin = snd . runAG (minS |*| rep) minI init
  where init (MinS i,_) = MinI i

repminG :: Dag IntTreeF -> Tree IntTreeF
repminG =  snd . runAGDag const (minS |*| rep) minI init
  where init (MinS i,_) = MinI i

rep' ::  (MinI :< atts) => Rewrite IntTreeF atts IntTreeF
rep' (Leaf i)    =  In (Leaf globMin)
rep' (Node a b)  =  In (Node (Ret a) (Ret b))

repmin' :: Tree IntTreeF -> Tree IntTreeF
repmin' = snd . runRewrite minS minI rep' init
  where init (MinS i) = MinI i

repminG' :: Dag IntTreeF -> Dag IntTreeF
repminG' = snd . runRewriteDag const minS minI rep' init
  where init (MinS i) = MinI i

repminTestG1  = repminG i1
-- repminTestG1' = repminG' i1
repminTestT1  = repmin (unravelDag i1)

repminTestG2  = repminG i2
-- repminTestG2' = repminG' i2
repminTestT2  = repmin (unravelDag i2)
