{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Projection (pr, (:<)) where

import Prelude hiding (Either (..))

-- | Path to a node in a binary tree.
data Pos = Here | Left Pos | Right Pos

-- | Result of searching for a unique occurrence of a node in a binary tree.
data RPos = NotFound | Ambiguous | Found Pos

-- | Reconciling search results of two subtrees.
--   'Ambiguous' is the absorptive (dominant) element.
--   'NotFound'  is the identity (neutral) element.
--   If element was 'Found' it both subtrees, the result is 'Ambiguous'.
type family Ch (l :: RPos) (r :: RPos) :: RPos where
    Ch (Found x) (Found y) = Ambiguous
    Ch Ambiguous y = Ambiguous
    Ch x Ambiguous = Ambiguous
    Ch (Found x) y = Found (Left x)
    Ch x (Found y) = Found (Right y)
    Ch x y = NotFound

-- | @Elem e p@ searches for type @e@ in a nested tuple type @p@
--   returning a path to its location if successful.
type family Elem (e :: *) (p :: *) :: RPos where
    Elem e e = Found Here
    Elem e (l,r) = Ch (Elem e l) (Elem e r)
    Elem e p = NotFound

-- | @Pointer pos e p@ holds if result @pos@ points to subtree @e@ in @p@.
data Pointer (pos :: RPos) e p where
    Phere  :: Pointer (Found Here) e e
    Pleft  :: Pointer (Found pos) e p -> Pointer (Found (Left  pos)) e (p,p')
    Pright :: Pointer (Found pos) e p -> Pointer (Found (Right pos)) e (p',p)

-- | @pr' path p@ extracts subtree @e@ pointed to by @path@ in tree @p@.
pr' :: Pointer pos e p -> p -> e
pr' Phere      e     = e
pr' (Pleft  p) (x,_) = pr' p x
pr' (Pright p) (_,y) = pr' p y

-- | A class to automatically construct valid pathes.
class GetPointer (pos :: RPos) e p where
    pointer :: Pointer pos e p

instance GetPointer (Found Here) e e where
    pointer = Phere

instance GetPointer (Found pos) e p => GetPointer (Found (Left pos)) e (p, p') where
    pointer = Pleft pointer

instance GetPointer (Found pos) e p => GetPointer (Found (Right pos)) e (p', p) where
    pointer = Pright pointer

type (e :< p) = GetPointer (Elem e p) e p

-- | If @e@ is a part of type @p@, witnessed by constraint @e :< p@,
--   project out the corresponding value.
pr :: forall e p . (e :< p) => p -> e
pr p = pr' (pointer :: Pointer (Elem e p) e p) p
