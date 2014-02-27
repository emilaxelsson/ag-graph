{-# LANGUAGE TypeFamilies, DataKinds, PolyKinds,
 UndecidableInstances, MultiParamTypeClasses, FlexibleInstances, 
 GADTs, FlexibleContexts, ScopedTypeVariables, TypeOperators, ConstraintKinds #-}

module Projection (pr, (:<)) where

import Prelude hiding (Either (..))

data Pos = Here | Left Pos | Right Pos

data RPos = NotFound | Ambiguous | Found Pos

type family Ch (l :: RPos) (r :: RPos) :: RPos where
    Ch (Found x) (Found y) = Ambiguous
    Ch Ambiguous y = Ambiguous
    Ch x Ambiguous = Ambiguous
    Ch (Found x) y = Found (Left x)
    Ch x (Found y) = Found (Right y)
    Ch x y = NotFound

type family Elem (e :: *) (p :: *) :: RPos where
    Elem e e = Found Here
    Elem e (l,r) = Ch (Elem e l) (Elem e r)
    Elem e p = NotFound

data Pointer (pos :: RPos) e p where
    Phere :: Pointer (Found Here) e e
    Pleft :: Pointer (Found pos) e p -> Pointer (Found (Left pos)) e (p,p')
    Pright :: Pointer (Found pos) e p -> Pointer (Found (Right pos)) e (p',p)

class GetPointer (pos :: RPos) e p where
    pointer :: Pointer pos e p

instance GetPointer (Found Here) e e where
    pointer = Phere

instance GetPointer (Found pos) e p => GetPointer (Found (Left pos)) e (p, p') where
    pointer = Pleft pointer

instance GetPointer (Found pos) e p => GetPointer (Found (Right pos)) e (p', p) where
    pointer = Pright pointer

pr' :: Pointer pos e p -> p -> e
pr' Phere e = e
pr' (Pleft p) (x,_) = pr' p x
pr' (Pright p) (_,y) = pr' p y

type (e :< p) = GetPointer (Elem e p) e p

pr :: forall e p . (e :< p) => p -> e
pr p = pr' (pointer :: Pointer (Elem e p) e p) p


example :: (Int,((Bool,[Int]),Int)) -> Bool
example = pr
