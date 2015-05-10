{-# LANGUAGE TypeOperators #-}
module PAG.Product where

import Control.Applicative
import Control.Monad hiding (mapM,sequence)
import Data.Traversable (Traversable(..))
import Data.Foldable (Foldable(..))
import Prelude hiding (foldr,foldl,mapM,sequence)

infixr 8 :*:

-- |Formal product of signatures (functors).
data (f :*: g) a = f a :*: g a


ffst :: (f :*: g) a -> f a
ffst (x :*: _) = x

fsnd :: (f :*: g) a -> g a
fsnd (_ :*: x) = x

instance (Functor f, Functor g) => Functor (f :*: g) where
    fmap h (f :*: g) = (fmap h f :*: fmap h g)


instance (Foldable f, Foldable g) => Foldable (f :*: g) where
    foldr f e (x :*: y) = foldr f (foldr f e y) x
    foldl f e (x :*: y) = foldl f (foldl f e x) y


instance (Traversable f, Traversable g) => Traversable (f :*: g) where
    traverse f (x :*: y) = liftA2 (:*:) (traverse f x) (traverse f y)
    sequenceA (x :*: y) = liftA2 (:*:)(sequenceA x) (sequenceA y)
    mapM f (x :*: y) = liftM2 (:*:) (mapM f x) (mapM f y)
    sequence (x :*: y) = liftM2 (:*:) (sequence x) (sequence y)
