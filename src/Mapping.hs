{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Mapping
    ( Numbered (..)
    , o
    , unNumbered
    , number
    , Traversable ()
    , Mapping (..)
    , prodMap
    , lookupNumMap
    , lookupNumMap'
    , NumMap) where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Traversable
import Data.Foldable

import Control.Monad.State hiding (mapM)
import Prelude hiding (mapM)


-- | This type is used for numbering components of a functorial value.
data Numbered a = Numbered Int a

unNumbered :: Numbered a -> a
unNumbered (Numbered _ x) = x


-- | This function numbers the components of the given functorial
-- value with consecutive integers starting at 0.
number :: Traversable f => f c -> f (Numbered c)
number x = evalState (mapM run x) 0 where
  run :: c -> State Int (Numbered c)
  run b = do n <- get
             put (n+1)
             return $ Numbered n b


infix 1 |->
infixr 0 &


class Traversable m => Mapping m k | m -> k where
    -- | left-biased union of two mappings.
    (&) :: m v -> m v -> m v

    -- | This operator constructs a singleton mapping.
    (|->) :: k -> v -> m v

    -- | This is the empty mapping.
    empty :: m v

    -- | This function constructs the pointwise product of two maps each
    -- with a default value.
    prodMapWith :: (v1 -> v2 -> v) -> v1 -> v2 -> m v1 -> m v2 -> m v

    -- | Returns the value at the given key or returns the given
    -- default when the key is not an element of the map.
    findWithDefault :: a -> k -> m a -> a


o :: Mapping m k => m v
o = empty

-- | This function constructs the pointwise product of two maps each
-- with a default value.
prodMap :: Mapping m k => v1 -> v2 -> m v1 -> m v2 -> m (v1, v2)
prodMap = prodMapWith (,)

newtype NumMap k v = NumMap (IntMap v) deriving (Functor, Foldable, Traversable)

lookupNumMap :: a -> Int -> NumMap t a -> a
lookupNumMap d k (NumMap m) = IntMap.findWithDefault d k m

lookupNumMap' :: Int -> NumMap t a -> Maybe a
lookupNumMap' k (NumMap m) = IntMap.lookup k m

instance Mapping (NumMap k) (Numbered k) where
    NumMap m1 & NumMap m2 = NumMap (IntMap.union m1 m2)
    Numbered k _ |-> v = NumMap $ IntMap.singleton k v
    empty = NumMap IntMap.empty

    findWithDefault d (Numbered i _) m = lookupNumMap d i m

    prodMapWith f p q (NumMap mp) (NumMap mq) = NumMap $ IntMap.mergeWithKey merge 
                                          (IntMap.map (`f` q)) (IntMap.map (p `f`)) mp mq
      where merge _ p q = Just (p `f` q)
