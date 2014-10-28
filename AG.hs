{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE ImplicitParams            #-}
{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module AG
    ( module Projection
    , module AG
    ) where

import Control.Applicative
import Control.Monad.State.Strict

import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Traversable (Traversable)
import qualified Data.Traversable as Traversable

#if __GLASGOW_HASKELL__ > 706
import Projection
#else
import ProjectionSimple as Projection
#endif

-- * More notations for functorial action.

for = flip fmap
(<&>) = for


-- * Term trees as free monad over a signature functor.

-- | Free monad over functor @f@.
--   Or: the terms over signature @f@ and variables in @a@.
data Free f a
  = In (f (Free f a))
  | Ret a
  deriving (Functor, Foldable, Traversable)

instance Functor f => Applicative (Free f) where
  pure    = Ret
  Ret f <*> a = f <$> a
  In  t <*> a = In $ for t (<*> a)
  -- f <*> a = do
  --   f' <- f
  --   a' <- a
  --   return $ f' a'

instance Functor f => Monad (Free f) where
    return      = Ret
    Ret x >>= f = f x
    In t  >>= f = In $ for t (>>= f)

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
deriving instance Show (f (Tree f)) => Show (Tree f)

-- | Embedding closed terms into open terms.
freeTree :: Functor f => Tree f -> Free f a
freeTree = fmap zero


-- * Numbering nodes in a syntax tree.

-- | This type is used for numbering components of a functorial value.
data Numbered a = Numbered
  { theNumber  :: Int
  , unNumbered :: a
  }

-- | Return the current state and modify it.
strictModifyReturningOld :: MonadState s m => (s -> s) -> m s
strictModifyReturningOld f = do
  old <- get
  let new = f old
  new `seq` put new
  return old

-- | Return the current @Int@ state and increase it.
tick :: MonadState Int m => m Int
tick = strictModifyReturningOld (+1)

-- | This function numbers the components of the given functorial
-- value with consecutive integers starting at 0.
number :: Traversable f => f a -> f (Numbered a)
number t = Traversable.forM t (\ b -> tick <&> (`Numbered` b)) `evalState` 0


-- * Finite maps

infix 1 |->
infixr 0 &


-- | Abstract interface to finite maps.
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


-- | 'IntMap v' is a 'Mapping' from 'Int' to @v@.
instance Mapping IntMap Int where
    (&)   = IntMap.union
    (|->) = IntMap.singleton
    o     = IntMap.empty

    prodMap p q mp mq = IntMap.mergeWithKey merge
                        (IntMap.map (,q)) (IntMap.map (p,)) mp mq
      where merge _ p q = Just (p,q)

-- | 'NumMap t v' is a mapping from 'Numbered t' to @v@.
--   Note that @t@ is phantom type argument used to establish the
--   functional dependency @NumMap t v -> Numbered t@.
--   The actual map is from the unique 'Int' labels in @Numbered t@
--   to @v@.
newtype NumMap t v = NumMap {unNumMap :: IntMap v}

instance Mapping (NumMap t) (Numbered t) where
    NumMap m1 & NumMap m2 = NumMap $ m1 & m2
    Numbered k _t |-> v   = NumMap $ k |-> v
    o                     = NumMap $ o

    prodMap p q (NumMap mp) (NumMap mq) = NumMap $ prodMap p q mp mq

lookupNumMap :: v -> Int -> NumMap t v -> v
lookupNumMap d k (NumMap m) = IntMap.findWithDefault d k m


-- * Attribute grammars.

-- | This function provides access to components of the states from
--   "below" (i.e., the child nodes).

below :: (?below :: a -> q, p :< q) => a -> p
below = pr . ?below

-- | This function provides access to components of the state from
--   "above" (i.e., the parent nodes).

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
--   transformations. Both state transformations can depend mutually
--   recursive on each other.
--
--   In @runAg up down dInit@,
--
--   @down@ corresponds to the action for the downwards traversal
--   (computing the inherited attribute @d@),
--
--   @up@ corresponds to the action for the upwards traversal
--   (computing the synthesized attribute @u@), and
--
--   @dInit@ is a method to compute the initial inherited attribute
--   from the final synthesized attribute @uFinal@.

runAG :: Traversable f => Syn' f (u,d) u -> Inh' f (u,d) d -> (u -> d) -> Tree f -> u
runAG up down dInit t = uFinal
  where
    uFinal = run (dInit uFinal) t
    run d (In t) = u
      where
        -- Replace the numbered subtrees of t by
        -- a pair of synthesized and inherited value for this node.
        -- The inherited value @d'@ is read from the map @m@ and defaults to @d@.
        -- The synthesized value is computed by a recursive run, using the updated
        -- inherited value.
        t' = for (number t) $ \ (Numbered i s) ->
               let d' = lookupNumMap d i m
               in  Numbered i (run d' s, d')
        -- The map @m@ of inherited values is computed from @t'@ by the @down@ function.
        -- ?above = (u,d); ?below = unNumbered
        m = explicit down (u,d) unNumbered t'
        -- The result @u@ of the run on @t@ is computed by the @up@ function from o@t'@.
        u = explicit up   (u,d) unNumbered t'



-- | This combinator runs a stateful term homomorphisms with a state
-- space produced both on a bottom-up and a top-down state
-- transformation.

runRewrite :: (Traversable f, Functor g) =>
           Syn' f (u,d) u -> Inh' f (u,d) d ->
           Rewrite f (u,d) g ->
           (u -> d) -> Tree f -> (u, Tree g)
runRewrite up down trans dInit t = res
  where
    res@(uFin,_) = run (dInit uFin) t
    run d (In t) = (u, t'')
      where
        t' = for (number t) $ \ (Numbered i s) ->
               let d' = lookupNumMap d i m
                   (u', s') = run d' s
               in Numbered i ((u', d'), s')
        m = explicit down  (u,d) (fst . unNumbered) t'
        u = explicit up    (u,d) (fst . unNumbered) t'
        r = explicit trans (u,d) (fst . unNumbered) t'
        t'' = snd . unNumbered =<< r
