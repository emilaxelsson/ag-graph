{-# LANGUAGE MultiParamTypeClasses #-}

-- | A generic interface to constructs that bind or represent variables

module Variables where



import Data.Set

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

