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
import Data.List (genericLength)
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



type Name = Integer

data ExpF a
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
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance ShowConstr ExpF
  where
    showConstr (Var v)     = showVar v
    showConstr (LitB b)    = show b
    showConstr (LitI i)    = show i
    showConstr (Eq _ _)    = "Eq"
    showConstr (Add _ _)   = "Add"
    showConstr (Sub _ _)   = "Sub"
    showConstr (Mul _ _)   = "Mul"
    showConstr (If _ _ _)  = "If"
    showConstr (Let v _ _) = "Let " ++ showVar v
    showConstr (Arr _ v _) = "Arr " ++ showVar v

showVar :: Name -> String
showVar v = 'v' : show v

instance IsVar Name
  where
    newVar = id

instance HasVars ExpF Name
  where
    isVar (Var v) = Just v
    isVar _       = Nothing

    mkVar = Var

    bindsVars (Let v a b) = a |-> Set.empty & b |-> Set.singleton v
    bindsVars (Arr l v f) = l |-> Set.empty & f |-> Set.singleton v
    bindsVars _           = Dag.AG.empty

    renameVars (Let v (a,avs) (b,bvs)) =
        case (Set.toList avs, Set.toList bvs) of
          ([],[v']) -> Let v' a b
    renameVars (Arr (l,lvs) v (f,fvs)) =
        case (Set.toList lvs, Set.toList fvs) of
          ([],[v']) -> Arr l v' f
    renameVars f = fmap fst f

-- | The type of Feldspar expressions
newtype Data a = Data { unData :: Tree ExpF }

-- | Used to generate names for binding constructs; see \"Using Circular
-- Programs for Higher-Order Syntax\" (ICFP 2013,
-- <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)
maxBV :: Tree ExpF -> Name
maxBV (In (Let v a b)) = v `max` maxBV a
maxBV (In (Arr l v f)) = v `max` maxBV l
maxBV (In f)           = maximum $ (0:) $ Foldable.toList $ fmap maxBV f

share :: Data a -> (Data a -> Data b) -> Data b
share (Data a) f = Data $ In $ Let v a body
  where
    v    = maxBV body
    body = unData $ f $ Data $ In $ Var v

arr :: Data Integer -> (Data Integer -> Data a) -> Data [a]
arr (Data l) ixf = Data $ In $ Arr l v body
  where
    v    = maxBV body
    body = unData $ ixf $ Data $ In $ Var v

true, false :: Data Bool
true  = Data $ In $ LitB True
false = Data $ In $ LitB False

iff :: Data Bool -> Data a -> Data a -> Data a
iff (Data b) (Data x) (Data y) = Data $ In $ If b x y

instance Num (Data Integer)
  where
    fromInteger = Data . In . LitI . fromInteger
    Data x + Data y = Data $ In $ Add x y
    Data x - Data y = Data $ In $ Sub x y
    Data x * Data y = Data $ In $ Mul x y
    abs    = error "abs not implemented for Data Integer"
    signum = error "signum not implemented for Data Integer"

(<=>) :: Eq a => Data a -> Data a -> Data Bool
Data x <=> Data y = Data $ In $ Eq x y



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

(|--) :: SymTab env -> Tree ExpF -> Maybe (CompExp env)
gamma |-- In f = gamma |- f

(|-) :: SymTab env -> ExpF (Tree ExpF) -> Maybe (CompExp env)
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

ext :: (Name, Type a) -> SymTab env -> SymTab (a,env)
ext (v,t) gamma = Map.insert v (fst ::: t) (fmap shift gamma)
  where
    shift (get ::: u) = ((get . snd) ::: u)

compileIntOp
    :: (Integer -> Integer -> Integer)
    -> SymTab env
    -> Tree ExpF
    -> Tree ExpF
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
    Nothing + _     = Nothing
    _ + Nothing     = Nothing
    Just a + Just b = Just (a+b)

    Nothing - _     = Nothing
    _ - Nothing     = Nothing
    Just a - Just b = Just (a-b)

    Nothing * _     = Nothing
    _ * Nothing     = Nothing
    Just a * Just b = Just (a*b)

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
rangeMin (l1,u1) (l2,u2) = (min l1 l2, min u1 u2)

-- | Propagate ranges over the 'max' function
rangeMax :: Range -> Range -> Range
rangeMax (l1,u1) (l2,u2) = (max l1 l2, max u1 u2)



--------------------------------------------------------------------------------
-- * Transformation
--------------------------------------------------------------------------------

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

lookEnv :: Name -> Env Size -> Size
lookEnv n env = case Map.lookup n env of
    Nothing -> []
    Just sz -> sz

sizeOf ::  (?below :: a -> atts, Size :< atts) => a -> Size
sizeOf = below

sizeInfS :: (Env Size :< atts) => Syn ExpF atts Size
sizeInfS (Var v)     = lookEnv v above
sizeInfS (LitB _)    = []
sizeInfS (LitI i)    = [fromInteger i]
sizeInfS (Add a b)   = zipWith (+) (sizeOf a) (sizeOf b)
sizeInfS (Sub a b)   = zipWith (-) (sizeOf a) (sizeOf b)
sizeInfS (Mul a b)   = zipWith (*) (sizeOf a) (sizeOf b)
sizeInfS (Eq a b)    = []
sizeInfS (Min a b)   = zipWith rangeMin (sizeOf a) (sizeOf b)
sizeInfS (Max a b)   = zipWith rangeMax (sizeOf a) (sizeOf b)
sizeInfS (If _ t f)  = zipWith union (sizeOf t) (sizeOf f)
sizeInfS (Let _ _ b) = sizeOf b
sizeInfS (Arr l _ b) = sizeOf l ++ sizeOf b -- sizeOf l should have length 1

sizeInfI :: (Size :< atts) => Inh ExpF atts (Env Size)
sizeInfI (Let v a b) = b |-> Map.insert v (sizeOf a) above
sizeInfI (Arr l v b) = b |-> Map.insert v (sizeArrIx (sizeOf l)) above
sizeInfI _           = o

-- | Compute the size of the index in the expression @arr l (\i -> body)@, given
-- the size of @l@
sizeArrIx :: Size -> Size
sizeArrIx [szl] = [(0, upper (szl-1))]

sizeInf :: Tree ExpF -> Size
sizeInf = runAG sizeInfS sizeInfI (\ _ -> Map.empty)

sizeInfDag :: Dag ExpF -> Size
sizeInfDag = runAGDag trueIntersection sizeInfS sizeInfI (\ _ -> Map.empty)

viewSingleton :: Size -> Maybe Integer
viewSingleton [(Just l, Just u)] | l == u = Just l
viewSingleton _ = Nothing

simplifier :: (Size :< atts, Env Size :< atts) => Rewrite ExpF atts ExpF
simplifier (Add a b)
    | Just 0 <- viewSingleton (sizeOf a) = Ret b
    | Just 0 <- viewSingleton (sizeOf b) = Ret a
simplifier (Sub a b)
    | Just 0 <- viewSingleton (sizeOf b) = Ret a
simplifier (Mul a b)
    | Just 0 <- viewSingleton (sizeOf a) = In $ LitI 0
    | Just 0 <- viewSingleton (sizeOf b) = In $ LitI 0
    | Just 1 <- viewSingleton (sizeOf a) = Ret b
    | Just 1 <- viewSingleton (sizeOf b) = Ret a
simplifier (Eq a b)
    | Just True <- liftA2 (<=) ua lb = In $ LitB False
    | Just True <- liftA2 (<=) ub la = In $ LitB False
  where
    [(la,ua)] = sizeOf a
    [(lb,ub)] = sizeOf b
simplifier (Min a b)
    | Just True <- liftA2 (<=) ua lb = Ret a
    | Just True <- liftA2 (<=) ub la = Ret b
  where
    [(la,ua)] = sizeOf a
    [(lb,ub)] = sizeOf b
simplifier (Max a b)
    | Just True <- liftA2 (<=) ua lb = Ret b
    | Just True <- liftA2 (<=) ub la = Ret a
  where
    [(la,ua)] = sizeOf a
    [(lb,ub)] = sizeOf b
simplifier f = simpCxt f

simplify :: Tree ExpF -> Tree ExpF
simplify = snd . runRewrite
    sizeInfS
    sizeInfI
    simplifier
    (const Map.empty)

rename' :: Dag ExpF -> Dag ExpF
rename' = rename (Just (0 :: Name))

simplifyDag :: Dag ExpF -> Dag ExpF
simplifyDag
    = snd
    . runRewriteDag
        trueIntersection
        sizeInfS
        sizeInfI
        simplifier
        (const Map.empty)
    . rename'

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

-- | 'simplify' and 'simplifyDag' give the same result
prop_simplifyDag :: Data a -> Bool
prop_simplifyDag d = dsimp == dsimpg
  where
    dsimp  = simplify (unData d)
    dsimpg = unravelDag $ simplifyDag $ unsafePerformIO $ reifyDag $ unData d



--------------------------------------------------------------------------------
-- * Render AST
--------------------------------------------------------------------------------

renderAST :: Data a -> FilePath -> IO ()
renderAST d file = do
    dag <- reifyDag $ unData d
    renderDag dag file

renderAST_simp :: Data a -> FilePath -> IO ()
renderAST_simp d file = do
    dag <- reifyDag $ unData d
    renderDag (simplifyDag dag) file

astToSvg :: Data a -> IO ()
astToSvg d = do
    tmpd <- getTemporaryDirectory
    let tmpf = tmpd </> "523452345234"
    renderAST d tmpf
    system $ "dot -Tsvg " ++ tmpf ++ " -o ast.svg"
    return ()

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

ex1 :: Data [Integer]
ex1 = arr 10 $ \i -> let a = i+tre+4 in iff (a<=>tre) (let b = a+2 in b+b*b) (a+tre)
  where
    tre = 0*4

test1      = astToSvg ex1
test1_simp = astToSvg_simp ex1

data Ex c
  where
    Ex :: Typeable a => c a -> Ex c

testAll
    | allOK     = putStrLn "All tests passed"
    | otherwise = putStrLn "Failed"
  where
    es = [Ex ex1]
    allOK = all (\(Ex e) -> prop_sizeInf      e) es
         && all (\(Ex e) -> prop_sizeInfDag   e) es
         && all (\(Ex e) -> prop_simplifyEval e) es
         && all (\(Ex e) -> prop_simplifyDag  e) es

