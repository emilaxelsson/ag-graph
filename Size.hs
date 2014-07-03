{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeOperators #-}

-- | This module implements a size inference analysis, which attempts to assign an upper bound to
-- each Int-valued sub-expression. It demonstrates another example (than type inference) of an AG
-- where correspondence by monotonicity gives a meaningful result. The result is as for type
-- inference: if we get an upper bound from `sizeInfG`, then we get the same upper bound for
-- `sizeInf`.

module Size where



import Control.Monad
import Data.Foldable (Foldable)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (Traversable)

import AG
import Graph
import Paper (Name, trueIntersection)



data ExpF a = LitB' Bool | LitI' Int | Var' Name
            | Eq' a a    | Add' a a  | If' a a a
            | Let' Name a a  -- `Let v x y` means "let v be x in y"
  deriving (Eq, Show, Functor, Foldable, Traversable)

type Size = Maybe Int
type Env  = Map Name Size

lookEnv :: Name -> Env -> Size
lookEnv n = join . Map.lookup n

sizeOf ::  (?below :: a -> atts, Size :< atts) => a -> Size
sizeOf = below

sizeInfS :: (Env :< atts) => Syn ExpF atts Size
sizeInfS (LitB' _)    = Nothing
sizeInfS (LitI' i)    = Just i
sizeInfS (Eq' a b)    = Nothing
sizeInfS (Add' a b)   = do sa <- sizeOf a
                           sb <- sizeOf b
                           return (sa+sb)
sizeInfS (If' _ t f)  = do st <- sizeOf t
                           sf <- sizeOf f
                           return (max st sf)
sizeInfS (Var' v)     = lookEnv v above
sizeInfS (Let' v a b) = sizeOf b

sizeInfI :: (Size :< atts) => Inh ExpF atts Env
sizeInfI (Let' v a b) = b |-> Map.insert v (sizeOf a) above
sizeInfI _            = Map.empty

sizeInf :: Env -> Tree ExpF -> Size
sizeInf = runAG sizeInfS sizeInfI

sizeInfG :: Env -> Graph ExpF -> Size
sizeInfG = runAGGraph trueIntersection sizeInfS sizeInfI

-- let x = a+10 in if a==10 then x+10 else x
g1 = mkGraph 0
    [ (0, Let' "x" 1 4)
    , (1, Add' 2 3)
    , (2, Var' "a") -- free
    , (3, LitI' 10)
    , (4, If' 5 6 7)
    , (5, Eq' 2 3)
    , (6, Add' 7 3)
    , (7, Var' "x")
    ]

test1  = sizeInfG (Map.fromList [("a", Just 20)]) g1
test1T = sizeInf  (Map.fromList [("a", Just 20)]) $ unravelGraph g1

