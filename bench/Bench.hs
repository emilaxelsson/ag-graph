{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}



import Data.Monoid

import Criterion.Main
import Criterion.Config
import Control.DeepSeq

import AG
import Graph
import qualified GraphFree as Free
import Paper



--------------------------------------------------------------------------------
-- * Setup
--------------------------------------------------------------------------------

class Functor f => NFDataF f
  where
    rnfF :: NFData a => f a -> ()

instance NFData Zero where
    rnf _ = ()

instance (NFData a, NFDataF f) => NFData (Free f a)
  where
    rnf (In f) = rnfF f
    rnf (Ret x) = rnf x `seq` ()


instance NFDataF f => NFDataF (Free f)
  where
    rnfF (In f) = rnfF f
    rnfF (Ret x) = rnf x `seq` ()


instance NFDataF f => NFData (Graph f)
  where
    rnf (Graph r es n) = rnf r `seq` rnf n `seq` rnf (fmap rnfF es)


instance NFDataF IntTreeF
  where
    rnfF (Leaf l)   = rnf l `seq` ()
    rnfF (Node a b) = rnf a `seq` rnf b `seq` ()

expTree :: Int -> Tree IntTreeF
expTree 1 = In $ Leaf 10
expTree n = In $ Node (expTree (n-1)) (expTree (n-1))

expGraph :: Int -> Graph IntTreeF
expGraph = termTree . expTree

expGraphF :: Int -> Free.Graph IntTreeF
expGraphF = Free.termTree . expTree


linearGraph :: Int -> Graph IntTreeF
linearGraph n = mkGraph 0 $
    [(k, Node (k+1) (k+1)) | k <- [0..n-2] ] ++ [(n-1, Leaf 10)]

linearGraphF :: Int -> Free.Graph IntTreeF
linearGraphF n = mkGraph 0 $
    [(k, In $ Node (Ret (k+1)) (Ret (k+1))) | k <- [0..n-2] ] ++ [(n-1, In (Leaf 10))]




--------------------------------------------------------------------------------
-- * Reduce
--------------------------------------------------------------------------------

-- This benchmark is designed to be as simple as possible: only integer
-- attributes and simple semantic functions. This is to make be able to test the
-- efficiency of the run functions themselves.

newtype Value = Value Int deriving (Eq, Ord, Show, Num, Enum)
newtype Depth = Depth Int deriving (Eq, Ord, Show, Num, Enum)

value :: (Depth :< a) => Syn IntTreeF a Value
value (Leaf l) = Value (l+d)
  where
    Depth d = above
value (Node a b) = max (below a) (below b)

depth :: Inh IntTreeF a Depth
depth (Node a b) = a |-> d & b |-> d
  where
    d = above+1
depth _ = o

reduce :: Tree IntTreeF -> Int
reduce = fromEnum . runAG value depth 0

reduceG :: Graph IntTreeF -> Int
reduceG = fromEnum . runAGGraph max value depth 0

reduceGST :: Graph IntTreeF -> Int
reduceGST = fromEnum . runAGGraphST max value depth 0


reduceGF :: Free.Graph IntTreeF -> Int
reduceGF = fromEnum . Free.runAGGraph max value depth 0

reduceGFST :: Free.Graph IntTreeF -> Int
reduceGFST = fromEnum . Free.runAGGraphST max value depth 0

bench' str f arg = rnf arg `seq` bench str (nf f arg)

reduce_expTree n = bgroup "expTree"
    [bench' (show n) reduce $ expTree n | n <- [4..n]]
  -- Grows exponentially

reduce_expGraph n = bgroup "expGraph"
    [bench' (show n) reduceG $ expGraph n | n <- [4..n]]
  -- Grows exponentially. The overhead compared to `reduce` is about 6x for
  -- trees of size up to 2^16.

reduce_expGraphST n = bgroup "expGraphST"
    [bench' (show n) reduceGST $ expGraph n | n <- [4..n]]

reduce_expGraphF n = bgroup "expGraphF"
    [bench' (show n) reduceGF $ expGraphF n | n <- [4..n]]

reduce_expGraphFST n = bgroup "expGraphFST"
    [bench' (show n) reduceGFST $ expGraphF n | n <- [4..n]]


reduce_linearGraph n = bgroup "linearGraph"
    [bench' (show n) reduceG $ linearGraph n | n <- [4..n]]
  -- Grows linearly

reduce_linearGraphF n = bgroup "linearGraphF"
    [bench' (show n) reduceGF $ linearGraphF n | n <- [4..n]]
  -- Grows linearly


reduce_linearGraphBig n = bgroup "linearGraphBig"
    [bench' (show n) reduceG $ linearGraph n | n <- [10,20..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`

reduce_linearGraphBigST n = bgroup "linearGraphBigST"
    [bench' (show n) reduceGST $ linearGraph n | n <- [10,20..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`


reduce_linearGraphBigF n = bgroup "linearGraphBigF"
    [bench' (show n) reduceGF $ linearGraphF n | n <- [10,20..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`

reduce_linearGraphBigFST n = bgroup "linearGraphBigFST"
    [bench' (show n) reduceGFST $ linearGraphF n | n <- [10,20..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`


conf name = defaultConfig
    { cfgReport      = Last $ Just $ "reports/" ++ name ++ ".html"
    , cfgSummaryFile = Last $ Just $ "reports/" ++ name ++ ".csv"
    }



--------------------------------------------------------------------------------
-- * Repmin
--------------------------------------------------------------------------------

-- The results for `repmin` are quite consistent with those for `reduce`. One
-- important difference is that `repmin` produces a tree as result, which means
-- that simply forcing a bit result takes some time.

repmin_expTree n = bgroup "expTree"
    [bench' (show n) repmin $ expTree n | n <- [4..n]]
  -- Grows exponentially

repmin_expGraph n = bgroup "expGraph"
    [bench' (show n) repminG $ expGraph n | n <- [4..n]]
  -- Grows exponentially. The overhead compared to `repmin` is about 5x for
  -- trees of size up to 2^16.

repmin_expGraph' n = bgroup "expGraph'"
    [bench' (show n) repminG' $ expGraph n | n <- [4..n]]
  -- Grows exponentially. The overhead compared to `repmin` is about 70x for
  -- trees of size up to 2^12.

repmin_linearGraph n = bgroup "linearGraph"
    [bench' (show n) repminG $ linearGraph n | n <- [4..n]]

repmin_linearGraph' n = bgroup "linearGraph'"
    [bench' (show n) repminG' $ linearGraph n | n <- [4..n]]
  -- Grows linearly

repmin_linearGraphBig n = bgroup "linearGraphBig"
    [bench' (show n) repminG' $ linearGraph n | n <- [10,20..n]]
  -- Grows linearly even for sizes that are out of reach for `repmin`

main = do
    defaultMainWith (conf "reduce_overhead_expTree")     (return ()) [reduce_expTree        16]
    defaultMainWith (conf "reduce_overhead_expGraph")    (return ()) [reduce_expGraph       16]
    defaultMainWith (conf "reduce_overhead_expGraphST")    (return ()) [reduce_expGraphST       16]
    defaultMainWith (conf "reduce_overhead_expGraphF")   (return ()) [reduce_expGraphF      16]
    defaultMainWith (conf "reduce_overhead_expGraphFST")   (return ()) [reduce_expGraphFST      16]
    defaultMainWith (conf "reduce_sharing_expTree")      (return ()) [reduce_expTree        12]
    defaultMainWith (conf "reduce_sharing_expGraph")     (return ()) [reduce_expGraph       12]
    defaultMainWith (conf "reduce_sharing_expGraphST")     (return ()) [reduce_expGraphST       12]
    defaultMainWith (conf "reduce_sharing_expGraphF")    (return ()) [reduce_expGraphF      12]
    defaultMainWith (conf "reduce_sharing_linearGraph")  (return ()) [reduce_linearGraph    12]
    defaultMainWith (conf "reduce_sharing_linearGraphF") (return ()) [reduce_linearGraphF   12]
    defaultMainWith (conf "reduce_big_linearGraph")      (return ()) [reduce_linearGraphBig 200]
    defaultMainWith (conf "reduce_big_linearGraphST")      (return ()) [reduce_linearGraphBigST 200]
    defaultMainWith (conf "reduce_big_linearGraphF")     (return ()) [reduce_linearGraphBigF 200]
    defaultMainWith (conf "reduce_big_linearGraphFST")     (return ()) [reduce_linearGraphBigFST 200]

    defaultMainWith (conf "repmin_overhead_expTree")     (return ()) [repmin_expTree        16]
    defaultMainWith (conf "repmin_overhead_expGraph")    (return ()) [repmin_expGraph       16]
    defaultMainWith (conf "repmin_overhead_expGraph'")   (return ()) [repmin_expGraph'      12]  -- OBS only up to 12
    defaultMainWith (conf "repmin_sharing_expTree")      (return ()) [repmin_expTree        12]
    defaultMainWith (conf "repmin_sharing_expGraph")     (return ()) [repmin_expGraph       12]
    defaultMainWith (conf "repmin_sharing_linearGraph")  (return ()) [repmin_linearGraph    12]
    defaultMainWith (conf "repmin_sharing_linearGraph'") (return ()) [repmin_linearGraph    12]
    defaultMainWith (conf "repmin_big_linearGraph")      (return ()) [repmin_linearGraphBig 200]

