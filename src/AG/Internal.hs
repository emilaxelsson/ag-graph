{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE Rank2Types     #-}
{-# LANGUAGE TypeOperators  #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  AG.Internal
-- Copyright   :  (c) 2014 Patrick Bahr, Emil Axelsson
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the types for attribute grammars along with
-- some utility functions.
--
--------------------------------------------------------------------------------

module AG.Internal where


import Mapping
import Tree
import Projection


-- | This function provides access to attributes of the immediate
-- children of the current node.

below :: (?below :: child -> q, p :< q) => child -> p
below = pr . ?below

-- | This function provides access to attributes of the current node

above :: (?above :: q, p :< q) => p
above = pr ?above

-- | Turns the explicit parameters @?above@ and @?below@ into explicit
-- ones.

explicit :: ((?above :: q, ?below :: a -> q) => b) -> q -> (a -> q) -> b
explicit x ab be = x where ?above = ab; ?below = be


-- | A simple rewrite function that may depend on (inherited and/or
-- synthesised) attributes.
type Rewrite f q g = forall a . (?below :: a -> q, ?above :: q) => f a -> Free g a


-- | The type of semantic functions for synthesised attributes. For
-- defining semantic functions use the type 'Syn', which includes the
-- synthesised attribute that is defined by the semantic function into
-- the available attributes.

type Syn' f p q = forall a . (?below :: a -> p, ?above :: p) => f a -> q

-- | The type of semantic functions for synthesised attributes.
type Syn  f p q = (q :< p) => Syn' f p q

-- | Combines the semantic functions for two synthesised attributes to
-- form a semantic function for the compound attribute consisting of
-- the two original attributes.

prodSyn :: (p :< c, q :< c)
             => Syn f c p -> Syn f c q -> Syn f c (p,q)
prodSyn sp sq t = (sp t, sq t)


-- | Combines the semantic functions for two synthesised attributes to
-- form a semantic function for the compound attribute consisting of
-- the two original attributes.

(|*|) :: (p :< c, q :< c)
             => Syn f c p -> Syn f c q -> Syn f c (p,q)
(|*|) = prodSyn




-- | The type of semantic functions for inherited attributes. For
-- defining semantic functions use the type 'Inh', which includes the
-- inherited attribute that is defined by the semantic function into
-- the available attributes.

type Inh' f p q = forall m i . (Mapping m i, ?below :: i -> p, ?above :: p)
                                => f i -> m q

-- | The type of semantic functions for inherited attributes.

type Inh f p q = (q :< p) => Inh' f p q

-- | Combines the semantic functions for two inherited attributes to
-- form a semantic function for the compound attribute consisting of
-- the two original attributes.

prodInh :: (p :< c, q :< c) => Inh f c p -> Inh f c q -> Inh f c (p,q)
prodInh sp sq t = prodMap above above (sp t) (sq t)


-- | Combines the semantic functions for two inherited attributes to
-- form a semantic function for the compound attribute consisting of
-- the two original attributes.

(>*<) :: (p :< c, q :< c, Functor f)
         => Inh f c p -> Inh f c q -> Inh f c (p,q)
(>*<) = prodInh
