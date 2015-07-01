{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TypeOperators         #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  PAG.Internal
-- Copyright   :  (c) 2014 Patrick Bahr, Emil Axelsson
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the types for parametric attribute grammars
-- along with some utility functions.
--
--------------------------------------------------------------------------------

module PAG.Internal 
    ( module PAG.Internal 
    , module I
    ) where


import Mapping
import Tree
import PAG.Projection
import AG.Internal as I (explicit) 

-- | This function provides access to attributes of the immediate
-- children of the current node.

below :: (?below :: child -> q a, p :< q) => child -> p a
below = pr . ?below

-- | This function provides access to attributes of the current node

above :: (?above :: q a, p :< q) => p a
above = pr ?above


-- | The type of semantic functions for synthesised attributes. For
-- defining semantic functions use the type 'Syn', which includes the
-- synthesised attribute that is defined by the semantic function into
-- the available attributes.

type Syn' f p q g = forall child a . (?below :: child -> p a, ?above :: p a) => f child -> q (Free g a)

-- | The type of semantic functions for synthesised attributes.
type Syn  f p q g = (q :< p) => Syn' f p q g

-- | Combines the semantic functions for two synthesised attributes to
-- form a semantic function for the compound attribute consisting of
-- the two original attributes.

prodSyn :: (p :< c, q :< c) => Syn f c p g -> Syn f c q g -> Syn f c (p :*: q) g
prodSyn sp sq t = (sp t :*: sq t)


-- | Combines the semantic functions for two synthesised attributes to
-- form a semantic function for the compound attribute consisting of
-- the two original attributes.

(|*|) :: (p :< c, q :< c)
             => Syn f c p g -> Syn f c q g -> Syn f c (p :*: q) g
(|*|) = prodSyn




-- | The type of semantic functions for inherited attributes. For
-- defining semantic functions use the type 'Inh', which includes the
-- inherited attribute that is defined by the semantic function into
-- the available attributes.

type Inh' f p q g = forall m i a . (Mapping m i, ?below :: i -> p a, ?above :: p a)
                                => f i -> m (q (Free g a))

-- | The type of semantic functions for inherited attributes.

type Inh f p q g = (q :< p) => Inh' f p q g

-- | Combines the semantic functions for two inherited attributes to
-- form a semantic function for the compound attribute consisting of
-- the two original attributes.

prodInh :: (p :< c, q :< c, Functor p, Functor q) => Inh f c p g -> Inh f c q g -> Inh f c (p :*: q) g
prodInh sp sq t = prodMapWith (:*:) (fmap Ret above) (fmap Ret above) (sp t) (sq t)


-- | Combines the semantic functions for two inherited attributes to
-- form a semantic function for the compound attribute consisting of
-- the two original attributes.

(>*<) :: (p :< c, q :< c, Functor p, Functor q)
         => Inh f c p g -> Inh f c q g -> Inh f c (p:*:q) g
(>*<) = prodInh
