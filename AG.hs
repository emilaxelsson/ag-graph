{-# LANGUAGE CPP                    #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ImplicitParams         #-}
{-# LANGUAGE IncoherentInstances    #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module AG
    ( module Projection
    , module AG
    ) where

#if __GLASGOW_HASKELL__ > 706
import Projection
#else
import ProjectionSimple as Projection
#endif

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Traversable
import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable



import Control.Monad.State.Strict hiding (mapM)
import Prelude hiding (mapM)


data Free f a = In (f (Free f a))
              | Ret a

deriving instance Show (f (Tree f)) => Show (Tree f)


simpCxt :: Functor f => f a -> Free f a
simpCxt = In . fmap Ret

instance Functor f => Functor (Free f) where
    fmap f (Ret x) = Ret (f x)
    fmap f (In t) = In (fmap (fmap f) t)

instance Foldable f => Foldable (Free f) where
    foldr op c a = run a c
        where run (Ret a) e = a `op` e
              run (In t) e = Foldable.foldr run e t

    foldl op = run
        where run e (Ret a) = e `op` a
              run e (In t) = Foldable.foldl run e t

    fold (Ret a) = a
    fold (In t) = Foldable.foldMap Foldable.fold t

    foldMap f = run
        where run (Ret a) = f a
              run (In t) = Foldable.foldMap run t


instance Functor f => Monad (Free f) where
    return = Ret
    (Ret x) >>= f = f x
    (In t) >>= f = In (fmap (>>= f) t)

data Zero

deriving instance Show Zero

type Tree g = Free g Zero

freeTree :: Functor f => Tree f -> Free f a
freeTree (In f) = In (fmap freeTree f)
freeTree (Ret x) = Ret (zero x)

zero :: Zero -> a
zero _ = error "zero"

-- | This type is used for numbering components of a functorial value.
data Numbered a = Numbered Int a

unNumbered :: Numbered a -> a
unNumbered (Numbered _ x) = x


-- | This function numbers the components of the given functorial
-- value with consecutive integers starting at 0.
number :: Traversable f => f a -> f (Numbered a)
number x = fst $ runState (mapM run x) 0 where
  run b = do n <- get
             let m = n+1
             m `seq` put m
             return $ Numbered n b

infix 1 |->
infixr 0 &


class Mapping m k | m -> k where
    -- | left-biased union of two mappings.
    (&) :: m v -> m v -> m v

    -- | This operator constructs a singleton mapping.
    (|->) :: k -> v -> m v

    -- | This is the empty mapping.
    o :: m v

    -- | This function constructs the pointwise product of two maps each
    -- with a default value.
    prodMap :: v1 -> v2 -> m v1 -> m v2 -> m (v1, v2)


newtype NumMap k v = NumMap {unNumMap :: IntMap v}

lookupNumMap :: a -> Int -> NumMap t a -> a
lookupNumMap d k (NumMap m) = IntMap.findWithDefault d k m

instance Mapping (NumMap k) (Numbered k) where
    NumMap m1 & NumMap m2 = NumMap (IntMap.union m1 m2)
    Numbered k _ |-> v = NumMap $ IntMap.singleton k v
    o = NumMap IntMap.empty

    prodMap p q (NumMap mp) (NumMap mq) = NumMap $ IntMap.mergeWithKey merge 
                                          (IntMap.map (,q)) (IntMap.map (p,)) mp mq
      where merge _ p q = Just (p,q)


instance Mapping IntMap Int where
    (&) = IntMap.union
    (|->) = IntMap.singleton
    o = IntMap.empty

    prodMap p q mp mq = IntMap.mergeWithKey merge 
                        (IntMap.map (,q)) (IntMap.map (p,)) mp mq
      where merge _ p q = Just (p,q)


-- | This function provides access to components of the states from
-- "below".

below :: (?below :: a -> q, p :< q) => a -> p
below = pr . ?below

-- | This function provides access to components of the state from
-- "above"

above :: (?above :: q, p :< q) => p
above = pr ?above

-- | Turns the explicit parameters @?above@ and @?below@ into explicit
-- ones.

explicit :: ((?above :: q, ?below :: a -> q) => b) -> q -> (a -> q) -> b
explicit x ab be = x where ?above = ab; ?below = be



type Rewrite f q g = forall a . (?below :: a -> q, ?above :: q) => f a -> Free g a

type RewriteExpl f q g = forall a . q -> (a -> q) -> f a -> Free g a


-- | Definition of a synthesized attribute.

type Syn' f p q = forall a . (?below :: a -> p, ?above :: p) => f a -> q
type Syn  f p q = (q :< p) => Syn' f p q
type SynExpl f p q = forall a . p -> (a -> p) -> f a -> q

prodSyn :: (p :< c, q :< c)
             => Syn f c p -> Syn f c q -> Syn f c (p,q)
prodSyn sp sq t = (sp t, sq t)

(|*|) :: (p :< c, q :< c)
             => Syn f c p -> Syn f c q -> Syn f c (p,q)
(|*|) = prodSyn



-- | Definition of an inherited attribute
type Inh' f p q = forall m i . (Mapping m i, ?below :: i -> p, ?above :: p)
                                => f i -> m q
type Inh f p q = (q :< p) => Inh' f p q

type InhExpl f p q = forall m i . Mapping m i => p -> (i -> p) -> f i -> m q

prodInh :: (p :< c, q :< c)
               => Inh f c p -> Inh f c q -> Inh f c (p,q)
prodInh sp sq t = prodMap above above (sp t) (sq t)

-- | This is a synonym for 'prodInh'.

(>*<) :: (p :< c, q :< c, Functor f)
         => Inh f c p -> Inh f c q -> Inh f c (p,q)
(>*<) = prodInh



-- | This combinator combines a bottom-up and a top-down state
-- transformations. Both state transformations can depend mutually
-- recursive on each other.

runAG :: Traversable f => Syn' f (u,d) u -> Inh' f (u,d) d -> d -> Tree f -> u
runAG up down d (In t) = u where
        t' = fmap bel $ number t
        bel (Numbered i s) =
            let d' = lookupNumMap d i m
            in Numbered i (runAG up down d' s, d')
        m = explicit down (u,d) unNumbered t'
        u = explicit up (u,d) unNumbered t'

runAG' :: Traversable f => Syn' f (u,d) u -> Inh' f (u,d) d -> (u -> d) -> Tree f -> u
runAG' syn inh df t = let u = runAG syn inh d t
                          d = df u
                      in u

-- | This combinator runs a stateful term homomorphisms with a state
-- space produced both on a bottom-up and a top-down state
-- transformation.

runRewrite :: (Traversable f, Functor g) =>
           Syn' f (u,d) u -> Inh' f (u,d) d ->
           Rewrite f (u,d) g ->
           d -> Tree f -> (u, Tree g)
runRewrite up down trans d (In t) = (u,t'') where
        t' = fmap bel $ number t
        bel (Numbered i s) =
            let d' = lookupNumMap d i m
                (u', s') = runRewrite up down trans d' s
            in Numbered i ((u', d'),s')
        m = explicit down (u,d) (fst . unNumbered) t'
        u = explicit up (u,d) (fst . unNumbered) t'
        t'' = join $ fmap (snd . unNumbered) $ explicit trans (u,d) (fst . unNumbered) t'

runRewrite' :: (Traversable f, Functor g) =>
           Syn' f (u,d) u -> Inh' f (u,d) d ->
           Rewrite f (u,d) g ->
           (u -> d) -> Tree f -> (u, Tree g)
runRewrite' up down trans d' t = (u,t')
    where d      = d' u
          (u,t') = runRewrite up down trans d t
