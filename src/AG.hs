{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}


--------------------------------------------------------------------------------
-- |
-- Module      :  AG
-- Copyright   :  (c) 2014 Patrick Bahr, Emil Axelsson
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements recursion schemes derived from attribute
-- grammars.
--
--------------------------------------------------------------------------------

module AG
    ( runAG
    , runRewrite
    , module I
    )  where

import AG.Internal
import qualified AG.Internal as I hiding (explicit)
import Mapping as I
import Tree as I
import Projection as I




-- | This function runs an attribute grammar on a term. The result is
-- the (combined) synthesised attribute at the root of the term.

runAG :: forall f s i . Traversable f
      => Syn' f (s,i) s -- ^ semantic function of synthesised attributes
      -> Inh' f (s,i) i -- ^ semantic function of inherited attributes
      -> (s -> i)       -- ^ initialisation of inherited attributes
      -> Tree f         -- ^ input tree
      -> s
runAG syn inh init t = sFin where
    sFin = run iFin t
    iFin = init sFin
    run :: i -> Tree f -> s
    run i (In t) = s where
        bel (Numbered n c) =  let i' = lookupNumMap i n m
                              in Numbered n (run i' c, i')
        t'  = fmap bel (number t)
        m   = explicit inh (s,i) unNumbered t'
        s   = explicit syn (s,i) unNumbered t'


-- | This function runs an attribute grammar with rewrite function on
-- a term. The result is the (combined) synthesised attribute at the
-- root of the term and the rewritten term.

runRewrite :: forall f g u d . (Traversable f, Functor g)
           => Syn' f (u,d) u -> Inh' f (u,d) d -- ^ semantic function of synthesised attributes
           -> Rewrite f (u,d) g                -- ^ semantic function of inherited attributes
           -> (u -> d)                         -- ^ initialisation of inherited attributes
           -> Tree f                           -- ^ input term
           -> (u, Tree g)
runRewrite up down trans dinit t = res where
    res@(uFin,_) = run dFin t
    dFin = dinit uFin
    run :: d -> Tree f -> (u, Tree g)
    run d (In t) = (u,t'') where
        t' = fmap bel $ number t
        bel (Numbered i s) =
            let d' = lookupNumMap d i m
                (u', s') = run d' s
            in Numbered i ((u', d'),s')
        m = explicit down (u,d) (fst . unNumbered) t'
        u = explicit up (u,d) (fst . unNumbered) t'
        r = explicit trans (u,d) (fst . unNumbered) t'
        t'' = snd . unNumbered =<< r
