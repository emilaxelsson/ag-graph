{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

-- | A simplified version of the Feldspar EDSL. The simplifier is defined as a
-- rewriting attribute grammar, and works both for trees and DAGs.

module Feldspar where



import Control.Applicative
import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.List (genericLength, genericIndex)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Directory (getTemporaryDirectory)
import System.FilePath ((</>))
import System.IO.Unsafe (unsafePerformIO)
import System.Process (system)

import Variables
import Dag
import Dag.Render
import AG
import Dag.AG
import Dag.Rename
import Paper (trueIntersection)



--------------------------------------------------------------------------------
-- * Feldspar expressions
--------------------------------------------------------------------------------

-- | Variable names
type Name = Integer

-- | Functor for Feldspar expressions
data Feldspar a
    = Var Name
    | LitB Bool
    | LitI Integer
    | Add a a
    | Sub a a
    | Mul a a
    | Eq a a
    | Min a a
    | Max a a
    | If a a a
    | Let Name a a  -- `Let v x y` means "let v be x in y"
    | Arr a Name a  -- `Arr l i b` means `map (\i -> b) [0..l-1]`
    | Ix a a        -- `Ix arr i`  means `arr !! i`
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | For rendering
instance ShowConstr Feldspar
  where
    showConstr (Var v)     = showVar v
    showConstr (LitB b)    = show b
    showConstr (LitI i)    = show i
    showConstr (Add _ _)   = "Add"
    showConstr (Sub _ _)   = "Sub"
    showConstr (Mul _ _)   = "Mul"
    showConstr (Eq _ _)    = "Eq"
    showConstr (Min _ _)   = "Min"
    showConstr (Max _ _)   = "Max"
    showConstr (If _ _ _)  = "If"
    showConstr (Let v _ _) = "Let " ++ showVar v
    showConstr (Arr _ v _) = "Arr " ++ showVar v
    showConstr (Ix _ _)    = "Ix"

showVar :: Name -> String
showVar v = 'v' : show v

instance IsVar Name
  where
    newVar = id

instance HasVars Feldspar Name
  where
    isVar (Var v) = Just v
    isVar _       = Nothing

    mkVar = Var

    bindsVars (Let v a b) = a |-> Set.empty & b |-> Set.singleton v
    bindsVars (Arr l v b) = l |-> Set.empty & b |-> Set.singleton v
    bindsVars _           = Dag.AG.empty

    renameVars (Let v (a,avs) (b,bvs)) =
        case (Set.toList avs, Set.toList bvs) of
          ([],[v']) -> Let v' a b
    renameVars (Arr (l,lvs) v (f,fvs)) =
        case (Set.toList lvs, Set.toList fvs) of
          ([],[v']) -> Arr l v' f
    renameVars f = fmap fst f

instance EqConstr Feldspar
  where
    eqConstr (Var v1)    (Var v2)    = v1==v2
    eqConstr (LitB b1)   (LitB b2)   = b1==b2
    eqConstr (LitI i1)   (LitI i2)   = i1==i2
    eqConstr (Add _ _)   (Add _ _)   = True
    eqConstr (Sub _ _)   (Sub _ _)   = True
    eqConstr (Mul _ _)   (Mul _ _)   = True
    eqConstr (Eq _ _)    (Eq _ _)    = True
    eqConstr (Min _ _)   (Min _ _)   = True
    eqConstr (Max _ _)   (Max _ _)   = True
    eqConstr (If _ _ _)  (If _ _ _)  = True
    eqConstr (Let _ _ _) (Let _ _ _) = True
    eqConstr (Arr _ _ _) (Arr _ _ _) = True
    eqConstr (Ix _ _)    (Ix _ _)    = True
    eqConstr _ _ = False



--------------------------------------------------------------------------------
-- * Feldspar front end
--------------------------------------------------------------------------------

-- | The type of Feldspar expressions
newtype Data a = Data { unData :: Tree Feldspar }

-- | Boolean constants
true, false :: Data Bool
true  = Data $ In $ LitB True
false = Data $ In $ LitB False

instance Num (Data Integer)
  where
    fromInteger = Data . In . LitI . fromInteger
    Data x + Data y = Data $ In $ Add x y
    Data x - Data y = Data $ In $ Sub x y
    Data x * Data y = Data $ In $ Mul x y
    abs    = error "abs not implemented for Data Integer"
    signum = error "signum not implemented for Data Integer"

-- | Equality
(<=>) :: Eq a => Data a -> Data a -> Data Bool
Data x <=> Data y = Data $ In $ Eq x y

-- | Minimum of two integers
minn :: Data Integer -> Data Integer -> Data Integer
minn (Data a) (Data b) = Data $ In $ Min a b

-- | Maximum of two integers
maxx :: Data Integer -> Data Integer -> Data Integer
maxx (Data a) (Data b) = Data $ In $ Max a b

-- | Conditional expression
iff
    :: Data Bool  -- ^ Condition
    -> Data a     -- ^ True branch
    -> Data a     -- ^ False branch
    -> Data a
iff (Data b) (Data x) (Data y) = Data $ In $ If b x y

-- | Used to generate names for binding constructs; see \"Using Circular
-- Programs for Higher-Order Syntax\" (ICFP 2013,
-- <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)
maxBV :: Tree Feldspar -> Name
maxBV (In (Let v a b)) = v `max` maxBV a
maxBV (In (Arr l v f)) = v `max` maxBV l
maxBV (In f)           = maximum $ (0:) $ Foldable.toList $ fmap maxBV f

-- | Share a value in a computation
share :: Data a -> (Data a -> Data b) -> Data b
share (Data a) f = Data $ In $ Let v a body
  where
    v    = succ $ maxBV body
    body = unData $ f $ Data $ In $ Var v

-- | Array construction
arr
    :: Data Integer              -- ^ Length
    -> (Data Integer -> Data a)  -- ^ Index mapping
    -> Data [a]
arr (Data l) ixf = Data $ In $ Arr l v body
  where
    v    = succ $ maxBV body
    body = unData $ ixf $ Data $ In $ Var v

-- | Array indexing
(!) :: Data [a] -> Data Integer -> Data a
Data arr ! Data i = Data $ In $ Ix arr i



--------------------------------------------------------------------------------
-- * Evaluation
--------------------------------------------------------------------------------

-- This section implements "typed compilation". See "Efficient Evaluation for
-- Untyped and Compositional Representations of Expressions"
-- (<http://www.cse.chalmers.se/~emax/documents/axelsson2014efficient.pdf>)

data Type a
  where
    BoolType :: Type Bool
    IntType  :: Type Integer
    ListType :: Type a -> Type [a]

class Typeable a
  where
    typeRep :: Type a

instance               Typeable Bool    where typeRep = BoolType
instance               Typeable Integer where typeRep = IntType
instance Typeable a => Typeable [a]     where typeRep = ListType typeRep

data Wit c
  where
    Wit :: c => Wit c

typeEq :: Type a -> Type b -> Maybe (Wit (a ~ b))
typeEq BoolType BoolType = Just Wit
typeEq IntType  IntType  = Just Wit
typeEq (ListType ta) (ListType tb) = do
    Wit <- typeEq ta tb
    return Wit

witEq :: Type a -> Wit (Eq a)
witEq BoolType = Wit
witEq IntType  = Wit
witEq (ListType t)
    | Wit <- witEq t = Wit

data CompExp env where
    (:::) :: (env -> a) -> Type a -> CompExp env

-- | Environment for variables in scope
type Env a = Map Name a

type SymTab env = Env (CompExp env)

emptyTab :: SymTab ()
emptyTab = Map.empty

(|--) :: SymTab env -> Tree Feldspar -> Maybe (CompExp env)
gamma |-- In f = gamma |- f

(|-) :: SymTab env -> Feldspar (Tree Feldspar) -> Maybe (CompExp env)
gamma |- Var v   = Map.lookup v gamma
gamma |- LitB b  = return $ (\_ -> b) ::: BoolType
gamma |- LitI i  = return $ (\_ -> i) ::: IntType
gamma |- Add a b = compileIntOp (+) gamma a b
gamma |- Sub a b = compileIntOp (-) gamma a b
gamma |- Mul a b = compileIntOp (*) gamma a b
gamma |- Min a b = compileIntOp min gamma a b
gamma |- Max a b = compileIntOp max gamma a b
gamma |- Eq a b = do
    a' ::: ta <- gamma |-- a
    b' ::: tb <- gamma |-- b
    Wit       <- typeEq ta tb
    Wit       <- return $ witEq ta
    let run e = a' e == b' e
    return $ run ::: BoolType
gamma |- If c t f = do
    c' ::: BoolType <- gamma |-- c
    t' ::: tt       <- gamma |-- t
    f' ::: tf       <- gamma |-- f
    Wit             <- typeEq tt tf
    let run e = if c' e then t' e else f' e
    return $ run ::: tt
gamma |- Let v a b = do
    a' ::: ta <- gamma            |-- a
    b' ::: tb <- ext (v,ta) gamma |-- b
    return $ (\e -> b' (a' e, e)) ::: tb
gamma |- Arr l v b = do
    l' ::: IntType <- gamma                 |-- l
    b' ::: tb      <- ext (v,IntType) gamma |-- b
    let run e = map (\i -> b' (i,e)) [0 .. l' e - 1]
    return $ run ::: ListType tb
gamma |- Ix a i = do
    a' ::: ListType t <- gamma |-- a
    i' ::: IntType    <- gamma |-- i
    let run e = a' e `genericIndex` i' e
    return $ run ::: t

ext :: (Name, Type a) -> SymTab env -> SymTab (a,env)
ext (v,t) gamma = Map.insert v (fst ::: t) (fmap shift gamma)
  where
    shift (get ::: u) = ((get . snd) ::: u)

compileIntOp
    :: (Integer -> Integer -> Integer)
    -> SymTab env
    -> Tree Feldspar
    -> Tree Feldspar
    -> Maybe (CompExp env)
compileIntOp op gamma a b = do
    a' ::: IntType <- gamma |-- a
    b' ::: IntType <- gamma |-- b
    let run e = a' e `op` b' e
    return $ run ::: IntType

eval :: forall a . Typeable a => Data a -> a
eval (Data a) = (\(Just a) -> a) $ do
    a' ::: ta <- emptyTab |-- a
    Wit <- typeEq ta (typeRep :: Type a)
    return $ a' ()



--------------------------------------------------------------------------------
-- * Range propagation
--------------------------------------------------------------------------------

-- | (lower bound, upper bound)
type Range = (Maybe Integer, Maybe Integer)

-- | Lower bound of a range
lower :: Range -> Maybe Integer
lower = fst

-- | Upper bound of a range
upper :: Range -> Maybe Integer
upper = snd

-- | Range union
union :: Range -> Range -> Range
union (l1,u1) (l2,u2) = (min l1 l2, max u1 u2)

-- | Check whether the first range is contained in the second range
isSubRangeOf :: Range -> Range -> Bool
isSubRangeOf r1 r2 = union r1 r2 == r2

-- | Check whether the integer is in the given range
inRange :: Integer -> Range -> Bool
inRange i r = fromInteger i `isSubRangeOf` r

instance Num (Maybe Integer)
  where
    fromInteger = Just
    (+) = liftA2 (+)
    (-) = liftA2 (-)
    (*) = liftA2 (*)
    abs    = error "abs not implemented for Maybe Integer"
    signum = error "signum not implemented for Maybe Integer"

instance Num Range
  where
    fromInteger i     = (Just i, Just i)
    (l1,u1) + (l2,u2) = (l1+l2, u1+u2)
    (l1,u1) - (l2,u2) = (l1-u2, u1-l2)
    (l1,u1) * (l2,u2) = (minimum bounds, maximum bounds)
      where
        bounds = [l1*l2, l1*u2, u1*l2, u1*u2]
    abs    = error "abs not implemented for Range"
    signum = error "signum not implemented for Range"

-- | Propagate ranges over the 'min' function
rangeMin :: Range -> Range -> Range
rangeMin (l1,u1) (l2,u2) = (liftA2 min l1 l2, liftA2 min u1 u2)

-- | Propagate ranges over the 'max' function
rangeMax :: Range -> Range -> Range
rangeMax (l1,u1) (l2,u2) = (liftA2 max l1 l2, liftA2 max u1 u2)



--------------------------------------------------------------------------------
-- * Transformation
--------------------------------------------------------------------------------

-- | Make a Feldspar DAG well-scoped
renameFeld :: Dag Feldspar -> Dag Feldspar
renameFeld = rename (Just (0 :: Name))

-- | Alpha-equivalence of Feldspar trees
alphaEqFeld :: Tree Feldspar -> Tree Feldspar -> Bool
alphaEqFeld = alphaEq (Nothing :: Maybe Name)

-- | Size of an expression = over-approximation of the set of values it might
-- take on
--
-- The length of the list varies for different types:
--
-- * Integer expressions: 1
-- * Non-integer scalars: 0
-- * Arrays:              1 + the number of ranges of the element type
type Size = [Range]

-- | Check whether the integer is in the given size
inSize :: forall a . Typeable a => a -> Size -> Bool
inSize = go (typeRep :: Type a)
  where
    go :: Type b -> b -> Size -> Bool
    go BoolType _ _           = True
    go IntType  i [r]         = i `inRange` r
    go (ListType t) as (r:rs) =
        inRange (genericLength as) r && all (\a -> go t a rs) as

-- | Lookup the size of a given variable in the environment
lookEnv :: Name -> Env Size -> Size
lookEnv n env = case Map.lookup n env of
    Nothing -> error $ "lookEnv: variable " ++ show n ++ " not in scope"
    Just sz -> sz

-- | Get the inferred size of a sub-expression
sizeOf ::  (?below :: a -> atts, Size :< atts) => a -> Size
sizeOf = below

-- | Compute the synthesized 'Size' attribute for a node
sizeInfS :: (Env Size :< atts, Maybe Value :< atts) => Syn Feldspar atts Size
-- Sizes of variables are obtained from the environment
sizeInfS (Var v)   = lookEnv v above
sizeInfS (LitB _)  = []
sizeInfS (LitI i)  = [fromInteger i]
sizeInfS (Add a b) = zipWith (+) (sizeOf a) (sizeOf b)
sizeInfS (Sub a b) = zipWith (-) (sizeOf a) (sizeOf b)
sizeInfS (Mul a b) = zipWith (*) (sizeOf a) (sizeOf b)
sizeInfS (Eq a b)  = []
sizeInfS (Min a b) = zipWith rangeMin (sizeOf a) (sizeOf b)
sizeInfS (Max a b) = zipWith rangeMax (sizeOf a) (sizeOf b)
-- Reduce If when the condition is a constant:
sizeInfS (If b t f)
    | Just (Value BoolType b') <- valueOf b = sizeOf $ if b' then t else f
sizeInfS (If _ t f)  = zipWith union (sizeOf t) (sizeOf f)
sizeInfS (Let _ _ b) = sizeOf b
sizeInfS (Arr l _ b) = sizeOf l ++ sizeOf b -- sizeOf l should have length 1
sizeInfS (Ix arr i)  = tail (sizeOf arr)

-- | Compute the inherited variable environment attribute for the
-- sub-expressions of a node
sizeInfI :: (Size :< atts) => Inh Feldspar atts (Env Size)
-- Insert `v` with the size of `a` into the environment:
sizeInfI (Let v a b) = b |-> Map.insert v (sizeOf a) above
-- Insert `v` with the size [0 .. l-1] into the environment:
sizeInfI (Arr l v b) = b |-> Map.insert v (sizeArrIx (sizeOf l)) above
sizeInfI _           = o

-- | Compute the size of the index in the expression @arr l (\i -> body)@, given
-- the size of @l@
sizeArrIx :: Size -> Size
sizeArrIx [szl] = [(0, upper (szl-1))]

-- | Extract an integer when the size is a singleton range
viewSingleton :: Size -> Maybe Integer
viewSingleton [(Just l, Just u)] | l == u = Just l
viewSingleton _ = Nothing

-- | Union type for constant values
data Value
  where
    Value :: Type a -> a -> Value

-- | Get the folded value of a sub-expression
valueOf :: (?below :: a -> atts, Maybe Value :< atts) => a -> Maybe Value
valueOf = below

-- | Get the folded value of a sub-expression, projected to 'Bool'
valueOfB :: (?below :: a -> atts, Maybe Value :< atts) => a -> Maybe Bool
valueOfB a = do
    Value BoolType b <- below a
    return b

-- | Get the folded value of a sub-expression, projected to 'Integer'
valueOfI :: (?below :: a -> atts, Maybe Value :< atts) => a -> Maybe Integer
valueOfI a = do
    Value IntType i <- below a
    return i

-- | Compute the synthesized constant value of a node
constFoldS :: (Size :< atts) => Syn Feldspar atts (Maybe Value)
-- All integer cases are handled by getting the result from size inference:
constFoldS f | Just i <- viewSingleton above = Just $ Value IntType i
constFoldS (LitB b) = Just $ Value BoolType b
-- Constant folding for Eq:
constFoldS (Eq a b)
    | Just (Value ta a') <- valueOf a
    , Just (Value tb b') <- valueOf b
    , Just Wit           <- typeEq ta tb
    , Wit                <- witEq ta
    = Just $ Value BoolType (a' == b')
-- Reduce Eq when sizes of operands are disjoint:
constFoldS (Eq a b)
    | Just True <- liftA2 (<=) ua lb = Just $ Value BoolType False
    | Just True <- liftA2 (<=) ub la = Just $ Value BoolType False
  where
    [(la,ua)] = sizeOf a
    [(lb,ub)] = sizeOf b
-- Reduce If when the condition is a constant:
constFoldS (If b t f)
    | Just (Value BoolType b') <- valueOf b = valueOf $ if b' then t else f
constFoldS _ = Nothing

-- | Size inference for a Feldspar expression tree
sizeInf :: Tree Feldspar -> Size
sizeInf = fst . runAG (sizeInfS |*| constFoldS) sizeInfI (const Map.empty)

-- | Size inference for a Feldspar expression DAG
sizeInfDag :: Dag Feldspar -> Size
sizeInfDag
    = fst
    . runAGDag
        trueIntersection
        (sizeInfS |*| constFoldS)
        sizeInfI
        (const Map.empty)
    . renameFeld

-- | Simplify a node based on size inference and constant folding
simplifier :: (Size :< atts, Maybe Value :< atts, Env Size :< atts) =>
    Rewrite Feldspar atts Feldspar
-- Rewrite to a literal when constant folding says so:
simplifier _
    | Just (Value BoolType b) <- above = In $ LitB b
    | Just (Value IntType i)  <- above = In $ LitI i
simplifier (Add a b)
    | Just 0 <- valueOfI a = Ret b
    | Just 0 <- valueOfI b = Ret a
simplifier (Sub a b)
    | Just 0 <- valueOfI b = Ret a
simplifier (Mul a b)
    | Just 0 <- valueOfI a = In $ LitI 0
    | Just 0 <- valueOfI b = In $ LitI 0
    | Just 1 <- valueOfI a = Ret b
    | Just 1 <- valueOfI b = Ret a
-- Reduce Min when sizes of operands are disjoint:
simplifier (Min a b)
    | Just True <- liftA2 (<=) ua lb = Ret a
    | Just True <- liftA2 (<=) ub la = Ret b
  where
    [(la,ua)] = sizeOf a
    [(lb,ub)] = sizeOf b
-- Reduce Max when sizes of operands are disjoint:
simplifier (Max a b)
    | Just True <- liftA2 (<=) ua lb = Ret b
    | Just True <- liftA2 (<=) ub la = Ret a
  where
    [(la,ua)] = sizeOf a
    [(lb,ub)] = sizeOf b
-- Reduce If when the condition is a constant:
simplifier (If c t f)
    | Just (Value BoolType b) <- valueOf c = Ret $ if b then t else f
simplifier f = simpCxt f

-- | Simplify a Feldspar expression tree
simplify :: Tree Feldspar -> Tree Feldspar
simplify = snd . runRewrite
    (sizeInfS |*| constFoldS)
    sizeInfI
    simplifier
    (const Map.empty)

-- | Simplify a Feldspar expression DAG
simplifyDag :: Dag Feldspar -> Dag Feldspar
simplifyDag
    = snd
    . runRewriteDag
        trueIntersection
        (sizeInfS |*| constFoldS)
        sizeInfI
        simplifier
        (const Map.empty)
    . renameFeld

-- | 'sizeInf' is an over-approximation of 'eval'
prop_sizeInf :: Typeable a => Data a -> Bool
prop_sizeInf d = eval d `inSize` sizeInf (unData d)

-- | 'sizeInfDag' is an over-approximation of 'eval'
prop_sizeInfDag :: Typeable a => Data a -> Bool
prop_sizeInfDag d = eval d `inSize` sizeInfDag (unsafePerformIO $ reifyDag $ unData d)

-- | 'simplify' does not change semantics
prop_simplifyEval :: forall a . Typeable a => Data a -> Bool
prop_simplifyEval d
    | Wit <- witEq (typeRep :: Type a)
    = eval d == eval (Data $ simplify $ unData d)

-- | 'simplify' and 'simplifyDag' give equivalent results
prop_simplifyDag :: Data a -> Bool
prop_simplifyDag d = dsimp `alphaEqFeld` dsimpg
  where
    dsimp  = simplify (unData d)
    dsimpg = unravelDag $ simplifyDag $ unsafePerformIO $ reifyDag $ unData d



--------------------------------------------------------------------------------
-- * Render AST
--------------------------------------------------------------------------------

-- | Render a Feldspar expression as a Dot graph that captures the implicit
-- sharing in the expression
renderAST :: Data a -> FilePath -> IO ()
renderAST d file = do
    dag <- reifyDag $ unData d
    renderDag dag file

-- | Simplify and render a Feldspar expression as a Dot graph that captures the
-- implicit sharing in the expression
renderAST_simp :: Data a -> FilePath -> IO ()
renderAST_simp d file = do
    dag <- reifyDag $ unData d
    renderDag (simplifyDag dag) file

-- | Render a Feldspar expression as an SVG graph that captures the implicit
-- sharing in the expression. The resulting file is called `ast.svg`.
--
-- This function requires Graphviz to be installed.
astToSvg :: Data a -> IO ()
astToSvg d = do
    tmpd <- getTemporaryDirectory
    let tmpf = tmpd </> "523452345234"
    renderAST d tmpf
    system $ "dot -Tsvg " ++ tmpf ++ " -o ast.svg"
    return ()

-- | Simplify and render a Feldspar expression as an SVG graph that captures the
-- implicit sharing in the expression. The resulting file is called `ast.svg`.
--
-- This function requires Graphviz to be installed.
astToSvg_simp :: Data a -> IO ()
astToSvg_simp d = do
    tmpd <- getTemporaryDirectory
    let tmpf = tmpd </> "523452345234"
    renderAST_simp d tmpf
    system $ "dot -Tsvg " ++ tmpf ++ " -o ast.svg"
    return ()



--------------------------------------------------------------------------------
-- * Testing
--------------------------------------------------------------------------------

-- Demonstrate simplification of the shared node `a`
ex1 :: Data [Integer]
ex1 = let a = 2+3
      in  arr a $ \i -> a + a*i

test1      = astToSvg ex1
test1_simp = astToSvg_simp ex1

-- Demonstrate simplification of the shared node `x`. `x` appears in different
-- variable environments, and its simplification makes use of the size
-- information for variable `i`.
ex2 :: Data [Integer]
ex2 =
    arr 10 $ \i ->
      let x = maxx 20 i + i
          a = arr (i+30) $ \j -> j*x
          b = arr (i+30) $ \k -> k-x
      in  a!2 + b!3

test2      = astToSvg ex2
test2_simp = astToSvg_simp ex2

-- Demonstrate size-based simplification. The ranges of the expressions `a!2`
-- and `b!3+800` are disjoint, so the `iff` expression reduces to `x`.
ex3 :: Data [Integer]
ex3 =
    arr 10 $ \i ->
      let x = maxx 20 i
          a = arr (i+x) $ \j -> j*x
          b = arr (i+x) $ \k -> k-x
      in  iff (a!2 <=> (b!3+800)) 45 x

test3      = astToSvg ex3
test3_simp = astToSvg_simp ex3

data Ex c
  where
    Ex :: Typeable a => c a -> Ex c

testAll
    | allOK     = putStrLn "All tests passed"
    | otherwise = putStrLn "Failed"
  where
    es = [Ex ex1, Ex ex2, Ex ex3]
    allOK = all (\(Ex e) -> prop_sizeInf      e) es
         && all (\(Ex e) -> prop_sizeInfDag   e) es
         && all (\(Ex e) -> prop_simplifyEval e) es
         && all (\(Ex e) -> prop_simplifyDag  e) es

