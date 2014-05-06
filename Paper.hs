{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Paper where



import Data.Foldable (Foldable)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable)

import AG
import Graph



trueIntersection :: (Ord k, Eq v) => Map k v -> Map k v -> Map k v
trueIntersection = Map.mergeWithKey (\_ x1 x2 -> if x1 == x2 then Just x1 else Nothing)
                     (const Map.empty) (const Map.empty)



-- The code from the paper

--------------------------------------------------------------------------------
-- * leavesBelow
--------------------------------------------------------------------------------

data IntTree = Leaf' Int | Node' IntTree IntTree
  deriving (Eq, Show)

t =  let  a  =  Node (Node (Leaf 2) (Leaf 3)) (Leaf 4)
     in   Node a a

leavesBelow :: Int -> IntTree -> Set Int
leavesBelow d (Leaf' i)
    | d <= 0                 =  Set.singleton i
    | otherwise              =  Set.empty
leavesBelow d (Node' t1 t2)  =
    leavesBelow (d-1) t1 `Set.union` leavesBelow (d-1) t2

data IntTreeF a = Leaf Int | Node a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

leavesBelowI :: Inh IntTreeF atts Int
leavesBelowI (Leaf i)      = Map.empty
leavesBelowI (Node t1 t2)  = t1 |-> d' & t2 |-> d'
            where d' = above - 1

leavesBelowS :: (Int :< atts) => Syn IntTreeF atts (Set Int)
leavesBelowS (Leaf i)
    | (above :: Int) <= 0  =  Set.singleton i
    | otherwise            =  Set.empty
leavesBelowS (Node t1 t2)  =  below t1 `Set.union` below t2

leavesBelow' :: Int -> Tree IntTreeF -> Set Int
leavesBelow' = runAG leavesBelowS leavesBelowI

leavesBelowG :: Int -> Graph IntTreeF -> Set Int
leavesBelowG = runAGGraph min leavesBelowS leavesBelowI

i1 = mkGraph 0
    [ (0, Node 1 2)
    , (1, Node 2 3)
    , (2, Node 4 4)
    , (3, Leaf 10)
    , (4, Leaf 20)
    ]

intTreeTestG1 = leavesBelowG 3 i1
intTreeTestT1 = leavesBelow' 3 (unravelGraph i1)

i2 :: Graph IntTreeF
i2 = mkGraph 0
    [ (0, Node 2 1)
    , (1, Node 4 2)
    , (2, Node 3 5)
    , (3, Node 6 7)
    , (4, Leaf 5)
    , (5, Leaf 4)
    , (6, Leaf 24)
    , (7, Leaf 3)
    ]

intTreeTestG2 = leavesBelowG 3 i2
intTreeTestT2 = leavesBelow' 3 (unravelGraph i2)



--------------------------------------------------------------------------------
-- * Reference EDSL
--------------------------------------------------------------------------------

data  Exp  =  LitB Bool       -- Boolean literal
           |  LitI Int        -- Integer literal
           |  Eq Exp Exp      -- Equality
           |  Add Exp Exp     -- Addition
           |  If Exp Exp Exp  -- Condition
           |  Var Name        -- Variable
           |  Let Name Exp Exp
           |  Iter Name Exp Exp Exp
  deriving (Eq, Show)

type  Name = String

e1 =  let  a = Add (Var "x") (LitI 0)
      in   Eq a a

e1' = Eq  (Add (Var "x") (LitI 0))
          (Add (Var "x") (LitI 0))

double :: Exp -> Exp
double a = Add a a

e2 =  iterate double (LitI 5) !! 8

double' a = Let "a" a (Add (Var "a") (Var "a"))

e2' = iterate double' (LitI 5) !! 8

data  Type  = BoolType | IntType deriving (Eq, Show)
type  Env   = Map Name Type

typeInf' :: Env -> Exp -> Maybe Type
typeInf' env (LitB _)                    =  Just BoolType
typeInf' env (LitI _)                    =  Just IntType
typeInf' env (Eq a b)
  |  Just ta        <-  typeInf' env a
  ,  Just tb        <-  typeInf' env b
  ,  ta == tb                            =  Just BoolType
typeInf' env (Add a b)
  |  Just IntType   <-  typeInf' env a
  ,  Just IntType   <-  typeInf' env b   =  Just IntType
typeInf' env (If c t f)
  |  Just BoolType  <-  typeInf' env c
  ,  Just tt        <-  typeInf' env t
  ,  Just tf        <-  typeInf' env f
  ,  tt == tf                            =  Just tt
typeInf' env (Var v)                     =  lookEnv v env
typeInf' env (Iter v n i b)
  |  Just IntType   <-  typeInf' env n
  ,  ti'@(Just ti)  <-  typeInf' env i
  ,  Just tb        <-  typeInf' (insertEnv v ti' env) b
  ,  ti == tb                            =  Just tb
typeInf' _ _                             =  Nothing

insertEnv :: Name -> Maybe Type -> Env -> Env
insertEnv v Nothing   env  =  env
insertEnv v (Just t)  env  =  Map.insert v t env

lookEnv :: Name -> Env -> Maybe Type
lookEnv = Map.lookup

e3 = Iter "s" (LitI 5) (LitI 1) $ Add (Var "s") (LitI 2)



--------------------------------------------------------------------------------
-- * Type inference attribute grammar
--------------------------------------------------------------------------------

data ExpF a  =  LitB' Bool   |  LitI' Int  |  Var' Name
             |  Eq' a a      |  Add' a a   |  If' a a a
             |  Iter' Name a a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

typeOf ::  (?below :: a -> atts, Maybe Type :< atts) =>
           a -> Maybe Type
typeOf = below

typeInfS :: (Env :< atts) => Syn ExpF atts (Maybe Type)
typeInfS (LitB' _)                =  Just BoolType
typeInfS (LitI' _)                =  Just IntType
typeInfS (Eq' a b)
  |  Just ta        <-  typeOf a
  ,  Just tb        <-  typeOf b
  ,  ta == tb                     =  Just BoolType
typeInfS (Add' a b)
  |  Just  IntType  <-  typeOf a
  ,  Just  IntType  <-  typeOf b  =  Just IntType
typeInfS (If' c t f)
  |  Just BoolType  <-  typeOf c
  ,  Just tt        <-  typeOf t
  ,  Just tf        <-  typeOf f
  ,  tt == tf                     =  Just tt
typeInfS (Var' v)                 =  lookEnv v above
typeInfS (Iter' v n i b)          
  |  Just IntType   <-  typeOf n  
  ,  Just ti        <-  typeOf i
  ,  Just tb        <-  typeOf b
  ,  ti == tb                     =  Just tb
typeInfS _                        =  Nothing

typeInfI :: (Maybe Type :< atts) => Inh ExpF atts Env
typeInfI (Iter' v n i b)  =  b |-> insertEnv v ti above
                               where ti = typeOf i
typeInfI _                =  Map.empty

typeInf :: Env -> Tree ExpF -> Maybe Type
typeInf = runAG typeInfS typeInfI

typeInfG :: Env -> Graph ExpF -> Maybe Type
typeInfG = runAGGraph trueIntersection typeInfS typeInfI

g1 = mkGraph 0
    [ (0, Iter' "x" 1 1 2)
    , (1, LitI' 10)
    , (2, Add' 3 4)
    , (3, Iter' "y" 5 5 6)
    , (4, Var' "x")
    , (5, LitI' 5)
    , (6, Add' 5 4)
    ]

typeTestG1 = typeInfG Map.empty g1
typeTestT1 = typeInf Map.empty (unravelGraph g1)

g2 = mkGraph 0
    [ (0, Iter' "x" 1 2 3)
    , (1, LitI' 0)
    , (2, Iter' "x" 1 1 3)
    , (3, Var' "x")
    ]

typeTestG2 = typeInfG Map.empty g2
typeTestT2 = typeInf Map.empty (unravelGraph g2)

g3 = mkGraph 0
    [ (0, Add' 1 3)
    , (1, Iter' "x" 2 2 5)
    , (2, LitI' 10)
    , (3, Iter' "x" 4 4 5)
    , (4, LitB' False)
    , (5, Var' "x")
    ]

typeTestG3 = typeInfG Map.empty g3
typeTestT3 = typeInf Map.empty (unravelGraph g3)



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
minI _ = Map.empty

rep ::  (MinI :< atts) => Syn IntTreeF atts (Tree IntTreeF)
rep (Leaf i)    =  In (Leaf globMin)
rep (Node a b)  =  In (Node (below a) (below b))

repmin :: Tree IntTreeF -> Tree IntTreeF
repmin = snd . runAG' (minS |*| rep) minI init
  where init (MinS i,_) = MinI i

repminG :: Graph IntTreeF -> Tree IntTreeF
repminG =  snd . runAGGraph' const (minS |*| rep) minI init
  where init (MinS i,_) = MinI i

rep' ::  (MinI :< atts) => Rewrite IntTreeF atts IntTreeF
rep' (Leaf i)    =  In (Leaf globMin)
rep' (Node a b)  =  In (Node (Ret a) (Ret b))

repmin' :: Tree IntTreeF -> Tree IntTreeF
repmin' = snd . runRewrite' minS minI rep' init
  where init (MinS i) = MinI i 

repminG' :: Graph IntTreeF -> Graph IntTreeF
repminG' = snd . runRewriteGraph' const minS minI rep' init
  where init (MinS i) = MinI i 

repminTestG1  = repminG i1
repminTestG1' = repminG' i1
repminTestT1  = repmin (unravelGraph i1)

repminTestG2  = repminG i2
repminTestG2' = repminG' i2
repminTestT2  = repmin (unravelGraph i2)



--------------------------------------------------------------------------------
-- * Circuit
--------------------------------------------------------------------------------

type Circuit = Graph IntTreeF

newtype Delay  = Delay  Int  deriving (Eq,Ord,Show,Num)
newtype Load   = Load   Int  deriving (Eq,Ord,Show,Num)

gateDelay :: (Load :< atts) => Syn IntTreeF atts Delay
gateDelay (Leaf _)    = 0
gateDelay (Node a b)  =
  max (below a) (below b) + 10 + Delay l
    where Load l = above

gateLoad :: Inh IntTreeF atts Load
gateLoad (Node a b)  = a |-> 1 & b |-> 1
gateLoad _           = Map.empty

delay :: Circuit -> Load -> Delay
delay g l = runAGGraph (+) gateDelay gateLoad l g

delayTree :: Tree IntTreeF -> Load -> Delay
delayTree c l = runAG gateDelay gateLoad l c

circTestG1 = delay i1 3
circTestT1 = delayTree (unravelGraph i1) 3

circTestG2 = delay i2 3
circTestT2 = delayTree (unravelGraph i2) 3

