{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators             #-}

module Tree where

import Control.Applicative
import Data.Foldable
import Data.Traversable


-- * Term trees as free monad over a signature functor.

-- | Free monad over functor @f@.
--   Or: the terms over signature @f@ and variables in @a@.
data Free f a
  = In (f (Free f a))
  | Ret a
  deriving (Functor, Foldable, Traversable)

instance (Eq (f (Free f a)), Eq a) => Eq (Free f a) where
  Ret x == Ret y = x == y
  In f == In g   = f == g

newtype NewString = NewString String

instance Show NewString where
  show (NewString s) = s

instance (Show (f NewString), Functor f, Show a) => Show (Free f a)
  where
    show (Ret a) = show a
    show (In t) = show (fmap (NewString . show) t)


instance Functor f => Applicative (Free f) where
  pure    = Ret
  Ret f <*> a = f <$> a
  In  t <*> a = In $ fmap (<*> a) t
  -- f <*> a = do
  --   f' <- f
  --   a' <- a
  --   return $ f' a'

instance Functor f => Monad (Free f) where
    return      = Ret
    Ret x >>= f = f x
    In t  >>= f = In $ fmap (>>= f) t

-- | Creating a shallow term (all direct subterms are variables).
simpCxt :: Functor f => f a -> Free f a
simpCxt = In . fmap Ret


-- * Closed term trees.

-- | Empty type.
data Zero
deriving instance Show Zero

-- | Empty type elimination.
zero :: Zero -> a
zero _ = error "zero"

-- | Trees over functor @f@.
--   Or: closed terms over functor @f@ (no variables).
type Tree f = Free f Zero

-- | Embedding closed terms into open terms.
freeTree :: Functor f => Tree f -> Free f a
freeTree = fmap zero

appCxt :: Functor f => Free f (Free f a) -> Free f a
appCxt (In f)  = In (fmap appCxt f)
appCxt (Ret h) = h

-- | Pair a functor with an annotation
data (f :&: ann) a = f a :&: ann
  deriving (Eq, Show, Functor)

getAnn :: (f :&: ann) a -> ann
getAnn (_ :&: ann) = ann

dropAnn :: (f :&: ann) a -> f a
dropAnn (f :&: _) = f

dropAnnFree :: Functor f => Free (f :&: ann) a -> Free f a
dropAnnFree (In f)  = In $ fmap dropAnnFree $ dropAnn f
dropAnnFree (Ret a) = Ret a

