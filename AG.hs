{-# LANGUAGE Rank2Types, FlexibleContexts, ImplicitParams, GADTs, TypeOperators, MultiParamTypeClasses, IncoherentInstances, CPP, StandaloneDeriving, UndecidableInstances, FunctionalDependencies, TypeFamilies #-}

module AG
    ( module Projection
    , module AG
    ) where

#if __GLASGOW_HASKELL__ > 706
import Projection
#else
import ProjectionSimple as Projection
#endif

import Data.Traversable
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map

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
newtype Numbered a = Numbered (Int, a)

unNumbered :: Numbered a -> a
unNumbered (Numbered (_, x)) = x

instance Eq (Numbered a) where
    Numbered (i,_) == Numbered (j,_) = i == j

instance Ord (Numbered a) where
    compare (Numbered (i,_))  (Numbered (j,_)) = i `compare` j

-- | This function numbers the components of the given functorial
-- value with consecutive integers starting at 0.
number :: Traversable f => f a -> f (Numbered a)
number x = fst $ runState (mapM run x) 0 where
  run b = do n <- get
             let m = n+1
             m `seq` put m
             return $ Numbered (n,b)

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

-- | This type is needed to construct the product of two DTAs.

data ProdState p q = LState p
                   | RState q
                   | BState p q


instance Ord k => Mapping (Map k) k where
    (&) = Map.union
    (|->) = Map.singleton
    o = Map.empty

    prodMap p q mp mq = Map.map final $ Map.unionWith combine ps qs
      where 
          ps = Map.map LState mp
          qs = Map.map RState mq
          combine (LState p) (RState q) = BState p q
          combine (RState q) (LState p) = BState p q
          combine _ _                   = error "unexpected merging"
          final (LState p) = (p, q)
          final (RState q) = (p, q)
          final (BState p q) = (p,q)

newtype NumMap k v = NumMap {unNumMap :: IntMap v}

lookupNumMap :: Int -> NumMap t a -> a -> a
lookupNumMap k (NumMap m) d = IntMap.findWithDefault d k m

instance Mapping (NumMap k) (Numbered k) where
    NumMap m1 & NumMap m2 = NumMap (IntMap.union m1 m2)
    Numbered (k,_)|-> v = NumMap $ IntMap.singleton k v
    o = NumMap IntMap.empty

    prodMap p q (NumMap mp) (NumMap mq) = NumMap $ IntMap.map final $ IntMap.unionWith combine ps qs
      where 
          ps = IntMap.map LState mp
          qs = IntMap.map RState mq
          combine (LState p) (RState q) = BState p q
          combine (RState q) (LState p) = BState p q
          combine _ _                   = error "unexpected merging"
          final (LState p) = (p, q)
          final (RState q) = (p, q)
          final (BState p q) = (p,q)






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
        bel (Numbered (i,s)) =
            let d' = Map.findWithDefault d (Numbered (i,undefined)) m
            in Numbered (i, (runAG up down d' s, d'))
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
        bel (Numbered (i,s)) =
            let d' = Map.findWithDefault d (Numbered (i,undefined)) m
                (u', s') = runRewrite up down trans d' s
            in Numbered (i, ((u', d'),s'))
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
