{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}



module TypeInf where



import Data.Foldable (Foldable (..))
import qualified Data.Foldable as Foldable
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.Set as Set



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

instance EqConstr ExpF
  where
    eqConstr (LitB' b1)      (LitB' b2)      = b1==b2
    eqConstr (LitI' i1)      (LitI' i2)      = i1==i2
    eqConstr (Var' v1)       (Var' v2)       = v1==v2
    eqConstr (Eq' _ _)       (Eq' _ _)       = True
    eqConstr (Add' _ _)      (Add' _ _)      = True
    eqConstr (If' _ _ _)     (If' _ _ _)     = True
    eqConstr (Iter' _ _ _ _) (Iter' _ _ _ _) = True
    eqConstr _ _ = False

-- | Make the DAG well-scoped
rename' :: Dag ExpF -> Dag ExpF
rename' = rename (Just "")

alphaEq' :: Tree ExpF -> Tree ExpF -> Bool
alphaEq' = alphaEq (Nothing :: Maybe Name)

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
prop_rename1 g = unravelDag g `alphaEq'` unravelDag (rename' g)

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

