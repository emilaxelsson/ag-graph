{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Criterion.Main
import Control.DeepSeq

import AG
import Graph
import Paper



--------------------------------------------------------------------------------
-- * Setup
--------------------------------------------------------------------------------

class Functor f => NFDataF f
  where
    rnfF :: NFData a => f a -> ()

instance NFDataF f => NFData (Tree f)
  where
    rnf (In f) = rnfF f

instance NFDataF f => NFData (Graph f)
  where
    rnf (Graph r es n) = rnf r `seq` rnf n `seq` rnf (fmap rnfF es)

instance NFDataF IntTreeF
  where
    rnfF (Leaf l)   = rnf l `seq` ()
    rnfF (Node a b) = rnf a `seq` rnf b `seq` ()

linearTree :: Int -> Graph IntTreeF
linearTree n = mkGraph 0 $
    [(k, Node (k+1) (k+1)) | k <- [0..n-2] ] ++ [(n-1, Leaf 10)]



--------------------------------------------------------------------------------
-- * Repmin
--------------------------------------------------------------------------------

repminGG :: Graph IntTreeF -> Graph IntTreeF
repminGG = repminG' . termTree . unravelGraph

linearTreeSmall_G = bgroup "linearTreeSmall_G"
    [bench (show n) $ nf repminG $ linearTree n | n <- [4,6..14]]

linearTreeSmall_G' = bgroup "linearTreeSmall_G'"
    [bench (show n) $ nf repminG' $ linearTree n | n <- [4,6..20]]

linearTreeSmall_GG = bgroup "linearTreeSmall_GG"
    [bench (show n) $ nf repminGG $ linearTree n | n <- [4,6..14]]

linearTreeBig = bgroup "linearTreeBig"
    [bench (show n) $ nf repminG' $ linearTree n | n <- [10,20..50]]

main = defaultMain
    [ linearTreeSmall_G
    , linearTreeSmall_G'
    , linearTreeSmall_GG
    , linearTreeBig
    ]

