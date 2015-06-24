{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Circuit where

import LeavesBelow (IntTreeF (..),i1,i2)

import Dag.Internal
import AG
import Dag.AG


type Circuit = Dag IntTreeF

newtype Delay  = Delay  Int  deriving (Eq,Ord,Show,Num)
newtype Load   = Load   Int  deriving (Eq,Ord,Show,Num)

gateDelay :: (Load :< atts) => Syn IntTreeF atts Delay
gateDelay (Leaf _)    = 0
gateDelay (Node a b)  =
  max (below a) (below b) + 10 + Delay l
    where Load l = above

gateLoad :: Inh IntTreeF atts Load
gateLoad (Node a b)  = a |-> 1 & b |-> 1
gateLoad _           = o

delay :: Circuit -> Load -> Delay
delay g l = runAGDag (+) gateDelay gateLoad (const l) g

delayTree :: Tree IntTreeF -> Load -> Delay
delayTree c l = runAG gateDelay gateLoad (const l) c

circTestG1 = delay i1 3
circTestT1 = delayTree (unravelDag i1) 3

circTestG2 = delay i2 3
circTestT2 = delayTree (unravelDag i2) 3

