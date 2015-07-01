{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | A generic interface to constructs that bind or represent variables

module Variables
    ( IsVar (..)
    , HasVars (..)
    , EqConstr (..)
    , alphaEq
    ) where



import qualified Data.Foldable as Foldable
import Data.Set (Set)
import qualified Data.Set as Set

import Tree
import Mapping



class IsVar v where
    -- | Construct a variable from a fresh identifier
    newVar :: Integer -> v

class (Functor f, IsVar v) => HasVars f v where
    -- | Indicates whether the @f@ constructor is a variable.
    isVar :: f a -> Maybe v
    isVar _ = Nothing

    -- | Construct a variable expression
    mkVar :: v -> f a

    -- | Indicates the set of variables bound by the @f@ constructor
    -- for each argument of the constructor.
    bindsVars :: Mapping m a => f a -> m (Set v)
    bindsVars _ = Mapping.empty

    -- | Rename the variables bound by the @f@ constructor
    renameVars :: f (a, Set v) -> f a
    renameVars f = fmap fst f

class EqConstr f where
    eqConstr :: f a -> f a -> Bool

alphaEq' :: forall v f . (EqConstr f, HasVars f v, Traversable f, Eq v)
    => [(v,v)] -> Tree f -> Tree f -> Bool
alphaEq' env (In var1) (In var2)
    | Just v1 <- isVar var1
    , Just v2 <- isVar var2
    = case (lookup v1 env, lookup v2 env') of
        (Nothing, Nothing)   -> v1==v2  -- Free variables
        (Just v2', Just v1') -> v1==v1' && v2==v2'
        _                    -> False
  where
    env' = [(v2,v1) | (v1,v2) <- env]
alphaEq' env (In f) (In g)
    =  eqConstr f g
    && all (checkChildren env)
        ( zip
            (Foldable.toList $ number f)
            (Foldable.toList $ number g)
        )
  where
    checkChildren :: [(v,v)] -> (Numbered (Tree f), Numbered (Tree f)) -> Bool
    checkChildren env (Numbered i1 t1, Numbered i2 t2)
        = length vs1 == length vs2 && alphaEq' (zip vs1 vs2 ++ env) t1 t2
      where
        vs1 = Set.toList $ lookupNumMap Set.empty i1 (bindsVars $ number f)
        vs2 = Set.toList $ lookupNumMap Set.empty i2 (bindsVars $ number g)

-- | Alpha-equivalence
alphaEq :: forall proxy v f
    .  (EqConstr f, HasVars f v, Traversable f, Eq v)
    => proxy v -> Tree f -> Tree f -> Bool
alphaEq _ = alphaEq' ([] :: [(v,v)])

