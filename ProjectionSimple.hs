{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances, OverlappingInstances #-}

module ProjectionSimple where

class a :< b where
    pr :: b -> a

instance a :< a where
    pr = id


instance a :< (a,b) where
    pr = fst

instance a :< ((a,b),c) where
    pr = fst . fst

instance b :< ((a,b),c) where
    pr = snd . fst


instance (c :< b) => c :< (a,b) where
    pr = pr . snd
