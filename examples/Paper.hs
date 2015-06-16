{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Paper where



import Data.Foldable (Foldable (..))
import qualified Data.Foldable as Foldable
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable (..))
import Control.Monad
import Control.Applicative
import System.Directory (getTemporaryDirectory)
import System.FilePath ((</>))
import System.IO.Unsafe -- Only for testing
import System.Process (system)

import Variables
import Dag.Internal
import AG
import Dag.AG
import Dag.Rename
import Dag.Render



trueIntersection :: (Ord k, Eq v) => Map k v -> Map k v -> Map k v
trueIntersection = Map.mergeWithKey (\_ x1 x2 -> if x1 == x2 then Just x1 else Nothing)
                     (const Map.empty) (const Map.empty)



-- The code from the paper

--------------------------------------------------------------------------------
-- * leavesBelow
--------------------------------------------------------------------------------

data IntTree = Leaf' Int | Node' IntTree IntTree
  deriving (Eq, Show)

iNode x y = In (Node x y)
iLeaf i = In (Leaf i)

t =  let  a  =  Node (Node (Leaf 2) (Leaf 3)) (Leaf 4)
     in   Node a a

leavesBelow :: Int -> IntTree -> Set Int
leavesBelow d (Leaf' i)
    | d <= 0                 =  Set.singleton i
    | otherwise              =  Set.empty
leavesBelow d (Node' t1 t2)  =
    leavesBelow (d-1) t1 `Set.union` leavesBelow (d-1) t2

data IntTreeF a = Leaf Int | Node a a
  deriving (Eq, Show)

instance Foldable IntTreeF where
    foldr _ z (Leaf _) = z
    foldr f z (Node x y) = x `f` (y `f` z)

instance Functor IntTreeF where
    fmap _ (Leaf i) = Leaf i
    fmap f (Node x y) = Node (f x) (f y)

instance Traversable IntTreeF where
    mapM _ (Leaf i) = return (Leaf i)
    mapM f (Node x y) = liftM2 Node (f x) (f y)

    traverse _ (Leaf i) = pure (Leaf i)
    traverse f (Node x y) = liftA2 Node (f x) (f y)


leavesBelowI :: Inh IntTreeF atts Int
leavesBelowI (Leaf i)      = o
leavesBelowI (Node t1 t2)  = t1 |-> d' & t2 |-> d'
            where d' = above - 1

leavesBelowS :: (Int :< atts) => Syn IntTreeF atts (Set Int)
leavesBelowS (Leaf i)
    | (above :: Int) <= 0  =  Set.singleton i
    | otherwise            =  Set.empty
leavesBelowS (Node t1 t2)  =  below t1 `Set.union` below t2

leavesBelow' :: Int -> Tree IntTreeF -> Set Int
leavesBelow' d = runAG leavesBelowS leavesBelowI (const d)

leavesBelowG :: Int -> Dag IntTreeF -> Set Int
leavesBelowG d = runAGDag min leavesBelowS leavesBelowI (const d)

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


intTreeTestG1 = leavesBelowG 3 i1
intTreeTestT1 = leavesBelow' 3 (unravelDag i1)


intTreeTestG2 = leavesBelowG 3 i2
intTreeTestT2 = leavesBelow' 3 (unravelDag i2)



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

iIter n x y z = In (Iter' n x y z)
iAdd x y      = In (Add' x y)
iVar x        = In (Var' x)
iLitI l       = In (LitI' l)
iLitB l       = In (LitB' l)

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
typeInfI _                =  o

typeInf :: Env -> Tree ExpF -> Maybe Type
typeInf env = runAG typeInfS typeInfI (const env)

typeInfG :: Env -> Dag ExpF -> Maybe Type
typeInfG env = runAGDag trueIntersection typeInfS typeInfI (const env)


gt1 :: Tree ExpF
gt1 = iIter "x" x x (iAdd (iIter "y" z z (iAdd z y)) y)
    where x = iLitI 10
          y = iVar "x"
          z = iLitI 5

g1 :: Dag ExpF
g1 = unsafePerformIO $ reifyDag gt1

gt2 :: Tree ExpF
gt2 = iIter "x" x (iIter "x" x x y) y
    where x = iLitI 0
          y = iVar "x"

g2 :: Dag ExpF
g2 = unsafePerformIO $ reifyDag gt2

gt3 :: Tree ExpF
gt3 = iAdd (iIter "x" x x z) (iIter "x" y y z)
    where x = iLitI 10
          y = iLitB False
          z = iVar "x"

g3 :: Dag ExpF
g3 = unsafePerformIO $ reifyDag gt3


typeTestG1 = typeInfG Map.empty g1
typeTestT1 = typeInf Map.empty (unravelDag g1)


typeTestG2 = typeInfG Map.empty g2
typeTestT2 = typeInf Map.empty (unravelDag g2)


typeTestG3 = typeInfG Map.empty g3
typeTestT3 = typeInf Map.empty (unravelDag g3)



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

-- repminG' :: Dag IntTreeF -> Dag IntTreeF
-- repminG' = snd . runRewriteDagST const minS minI rep' init
--   where init (MinS i) = MinI i

repminTestG1  = repminG i1
-- repminTestG1' = repminG' i1
repminTestT1  = repmin (unravelDag i1)

repminTestG2  = repminG i2
-- repminTestG2' = repminG' i2
repminTestT2  = repmin (unravelDag i2)



--------------------------------------------------------------------------------
-- * Circuit
--------------------------------------------------------------------------------

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



--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

-- | To be able to render the DAGs using 'renderDag'
instance ShowConstr ExpF
  where
    showConstr (LitB' b)       = show b
    showConstr (LitI' i)       = show i
    showConstr (Var' v)        = v
    showConstr (Eq' _ _)       = "Eq"
    showConstr (Add' _ _)      = "Eq"
    showConstr (If' _ _ _)     = "Eq"
    showConstr (Iter' v _ _ _) = "Iter " ++ v

instance IsVar Name
  where
    newVar = ('v':) . show

instance HasVars ExpF Name
  where
    isVar (Var' v) = Just v
    isVar _        = Nothing

    mkVar = Var'

    bindsVars (Iter' v k i b)
        = k |-> Set.empty
        & i |-> Set.empty
        & b |-> Set.singleton v
    bindsVars _ = Dag.AG.empty

    renameVars (Iter' v (k,kvs) (i,ivs) (b,bvs)) =
        case (Set.toList kvs ++ Set.toList ivs, Set.toList bvs) of
          ([],[v']) -> Iter' v' k i b
    renameVars f = fmap fst f

-- | Make the DAG well-scoped
rename' :: Dag ExpF -> Dag ExpF
rename' = rename (Just "")

alphaEq' :: [(Name,Name)] -> Tree ExpF -> Tree ExpF -> Bool
alphaEq' env (In (Var' v1)) (In (Var' v2)) =
    case (lookup v1 env, lookup v2 env') of
      (Nothing, Nothing)   -> v1==v2  -- Free variables
      (Just v2', Just v1') -> v1==v1' && v2==v2'
      _                    -> False
  where
    env' = [(v2,v1) | (v1,v2) <- env]
alphaEq' env (In (Iter' v1 k1 i1 b1)) (In (Iter' v2 k2 i2 b2)) =
    alphaEq' env k1 k2 && alphaEq' env i1 i2 && alphaEq' ((v1,v2):env) b1 b2
alphaEq' env (In (LitB' b1))     (In (LitB' b2))     = b1==b2
alphaEq' env (In (LitI' i1))     (In (LitI' i2))     = i1==i2
alphaEq' env (In (Eq' a1 b1))    (In (Eq' a2 b2))    = alphaEq' env a1 a2 && alphaEq' env b1 b2
alphaEq' env (In (Add' a1 b1))   (In (Add' a2 b2))   = alphaEq' env a1 a2 && alphaEq' env b1 b2
alphaEq' env (In (If' c1 t1 f1)) (In (If' c2 t2 f2)) = alphaEq' env c1 c2 && alphaEq' env t1 t2 && alphaEq' env f1 f2
alphaEq' env _ _ = False

-- | Alpha-equivalence (for testing the renamer)
alphaEq :: Tree ExpF -> Tree ExpF -> Bool
alphaEq = alphaEq' []

-- | Like 'flatten' but adds the root as a node in the graph
flatten' :: Traversable f => Dag f -> (Node, IntMap (f Node), Int)
flatten' d = (n, IntMap.insert n f m, n+1)
  where
    (f,m,n) = flatten d

-- | List the variable occurrences along with their scopes. Each variable in the
-- scope is paired with the node at which it is bound.
scope :: Dag ExpF -> [(Name,Node)] -> [(Name, [(Name,Node)])]
scope g env = go env r
  where
    (r,es,_) = flatten' g

    go env n = case es IntMap.! n of
      Var' v -> [(v,env)]
      Iter' v k i b
          -> go env k
          ++ go env i
          ++ go ((v,n):[vn | vn <- env, fst vn /= v]) b
      f -> concat $ Foldable.toList $ fmap (go env) f

groups :: Ord k => [(k,a)] -> [[a]]
groups ks = Map.elems $ Map.fromListWith (++) [(k,[a]) | (k,a) <- ks]

allEq :: Eq a => [a] -> Bool
allEq []     = True
allEq (a:as) = all (==a) as

-- | Check that no single name is paired with two different nodes
checkVar :: [(Name,Node)] -> Bool
checkVar = all allEq . groups

-- | Check for well-scopedness according to the paper
isWellScoped :: Dag ExpF -> Bool
isWellScoped g = all checkVar $ fmap concat $ groups sc
  where
    sc = scope g []

-- | Renaming does not changes semantics
prop_rename1 g = unravelDag g `alphaEq` unravelDag (rename' g)

-- | Renaming does not decrease the number of edges
prop_rename2 g = length (IntMap.toList $ edges g) <= length (IntMap.toList $ edges $ rename' g)

-- | Renaming produces a well-scoped DAG
prop_rename3 g = isWellScoped $ rename' g

testRenamer
    | allOK     = putStrLn "All tests passed"
    | otherwise = putStrLn "Failed"
  where
    gs = [g1,g2,g3]
    allOK = all prop_rename1 gs
         && all prop_rename2 gs
         && all prop_rename3 gs

-- | Render a DAG as SVG
astToSvg :: Dag ExpF -> IO ()
astToSvg d = do
    tmpd <- getTemporaryDirectory
    let tmpf = tmpd </> "523452345234"
    renderDag d tmpf
    system $ "dot -Tsvg " ++ tmpf ++ " -o ast.svg"
    return ()

