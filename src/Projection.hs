{-# LANGUAGE CPP #-}

module Projection (module I) where

#if __GLASGOW_HASKELL__ > 706
import Projection.TypeFam as I
#else
import Projection.Simple as I
#endif
