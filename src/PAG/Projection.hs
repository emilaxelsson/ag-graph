{-# LANGUAGE CPP #-}

module PAG.Projection (module I) where

#if __GLASGOW_HASKELL__ > 706
import PAG.Projection.TypeFam as I
#else
import PAG.Projection.Simple as I
#endif
