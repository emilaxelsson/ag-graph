{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}


--------------------------------------------------------------------------------
-- |
-- Module      :  PAG
-- Copyright   :  (c) 2014 Patrick Bahr, Emil Axelsson
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements recursion schemes derived from attribute
-- grammars. The variant implemented in this module, called parametric
-- attribute grammars, generalises both attribute grammars and
-- attribute grammars with rewrite function (as implemented in
-- "AG").
--
--------------------------------------------------------------------------------

module PAG
    ( runPAG
    , module I
    )  where

import PAG.Internal
import PAG.Projection as I
import qualified PAG.Internal as I hiding (explicit)
import Mapping as I
import Tree as I




-- | This function runs a parametric attribute grammar on a term. The
-- result is the (combined) synthesised attribute at the root of the
-- term.

runPAG :: forall f u d g . (Traversable f, Functor g, Functor d, Functor u)
      => Syn' f (u :*: d) u g                -- ^ semantic function of synthesised attributes
      -> Inh' f (u :*: d) d g                -- ^ semantic function of inherited attributes
      -> (forall a . u a -> d (Free g a)) -- ^ initialisation of inherited attributes
      -> Tree f                              -- ^ input term
      -> u (Tree g)
runPAG up down dinit t = uFin where
    uFin = run dFin t
    dFin = fmap appCxt $ dinit uFin
    run :: d (Tree g) -> Tree f -> u (Tree g)
    run d (In t) = u where
        t' = fmap bel $ number t
        bel (Numbered i s) =
            let d' = lookupNumMap d i m
            in Numbered i (run d' s :*: d')
        m = fmap (fmap appCxt) $ explicit down (u :*: d) unNumbered t'
        u = fmap appCxt $ explicit up (u :*: d) unNumbered t'
