{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances, OverlappingInstances #-}

module PAG.Projection.Simple (pr, (:<),module PAG.Product) where

import PAG.Product

class a :< b where
    pr :: b i -> a i

instance a :< a where
    pr = id


instance a :< (a :*: b) where
    pr = ffst

instance a :< ((a :*: b) :*: c) where
    pr = ffst . ffst

instance b :< ((a :*: b) :*: c) where
    pr = fsnd . ffst


instance (c :< b) => c :< (a :*: b) where
    pr = pr . fsnd
