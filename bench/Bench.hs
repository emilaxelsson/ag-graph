{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}





import Criterion.Main

import Criterion.Types
import Control.DeepSeq

import AG
import Graph
import qualified GraphFree as Free
import qualified GraphFreeNonEmpty as FNE
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

instance NFDataF f => NFData (FNE.Graph f)
  where
    rnf (FNE.Graph r es n) = rnf r `seq` rnf n `seq` rnf (fmap rnfF es)


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

expGraphFNE :: Int -> FNE.Graph IntTreeF
expGraphFNE = FNE.termTree . expTree

linearGraph :: Int -> Graph IntTreeF
linearGraph n = mkGraph 0 $
    [(k, Node (k+1) (k+1)) | k <- [0..n-2] ] ++ [(n-1, Leaf 10)]

linearGraphF :: Int -> Free.Graph IntTreeF
linearGraphF n = mkGraph 0 $
    [(k, In $ Node (Ret (k+1)) (Ret (k+1))) | k <- [0..n-2] ] ++ [(n-1, In (Leaf 10))]

linearGraphFNE :: Int -> FNE.Graph IntTreeF
linearGraphFNE n = FNE.mkGraph 0 $
    [(k, Node (Ret (k+1)) (Ret (k+1))) | k <- [0..n-2] ] ++ [(n-1, Leaf 10)]




--------------------------------------------------------------------------------
-- * Reduce
--------------------------------------------------------------------------------

-- This benchmark is designed to be as simple as possible: only integer
-- attributes and simple semantic functions. This is to make be able to test the
-- efficiency of the run functions themselves.
--
-- The benchmark is run with different AG implementations and graph
-- representations. The suffix "F" indicates that the graph
-- representation from "GraphFree" is used. The suffix "ST" indicates
-- that the mutable vector implementation is used. The suffix "FNE"
-- indicates that the graph representation from "GraphFreeNonEmpty" is
-- used. The benchmarks mentioned in the paper use the mutable vector
-- implementation.


newtype Value = Value Int deriving (Eq, Ord, Show, Num, Enum)
newtype Depth = Depth Int deriving (Eq, Ord, Show, Num, Enum)

value :: (Depth :< a,Bool :< a) => Syn IntTreeF a Value
value (Leaf l) = Value (if above then l+d else d)
  where
    Depth d = above
value (Node a b) = max (below a) (below b)

depth :: Inh IntTreeF a Depth
depth (Node a b) = a |-> d & b |-> d
  where
    d = above+1
depth _ = o

isLeft :: Inh IntTreeF a Bool
isLeft (Node a b) = a |-> True & b |-> False
isLeft _ = o


reduce :: Tree IntTreeF -> Int
reduce = fromEnum . runAG value (depth >*< isLeft) (const (0,False))

reduceG :: Graph IntTreeF -> Int
reduceG = fromEnum . runAGGraph max value (depth >*< isLeft) (const (0,False))

reduceGST :: Graph IntTreeF -> Int
reduceGST = fromEnum . runAGGraphST max value (depth >*< isLeft) (const (0,False))


reduceGF :: Free.Graph IntTreeF -> Int
reduceGF = fromEnum . Free.runAGGraph max value (depth >*< isLeft) (const (0,False))

reduceGFST :: Free.Graph IntTreeF -> Int
reduceGFST = fromEnum . Free.runAGGraphST max value (depth >*< isLeft) (const (0,False))


reduceGFNE :: FNE.Graph IntTreeF -> Int
reduceGFNE = fromEnum . FNE.runAGGraph max value (depth >*< isLeft) (0,False)

reduceGFNEST :: FNE.Graph IntTreeF -> Int
reduceGFNEST = fromEnum . FNE.runAGGraphST max value (depth >*< isLeft) (0,False)

bench' str f arg = rnf arg `seq` bench str (nf f arg)

reduce_expTree n = bgroup "expTree"
    [bench' (show n) reduce $ expTree n | n <- [12..n]]
  -- Grows exponentially

reduce_expGraph n = bgroup "expGraph"
    [bench' (show n) reduceG $ expGraph n | n <- [12..n]]
  -- Grows exponentially. The overhead compared to `reduce` is about 6x for
  -- trees of size up to 2^16.

reduce_expGraphST n = bgroup "expGraphST"
    [bench' (show n) reduceGST $ expGraph n | n <- [12..n]]

reduce_expGraphF n = bgroup "expGraphF"
    [bench' (show n) reduceGF $ expGraphF n | n <- [12..n]]

reduce_expGraphFNE n = bgroup "expGraphFNE"
    [bench' (show n) reduceGFNE $ expGraphFNE n | n <- [12..n]]


reduce_expGraphFST n = bgroup "expGraphFST"
    [bench' (show n) reduceGFST $ expGraphF n | n <- [12..n]]

reduce_expGraphFNEST n = bgroup "expGraphFNEST"
    [bench' (show n) reduceGFNEST $ expGraphFNE n | n <- [12..n]]


reduce_linearGraph n = bgroup "linearGraph"
    [bench' (show n) reduceG $ linearGraph n | n <- [12..n]]
  -- Grows linearly

reduce_linearGraphF n = bgroup "linearGraphF"
    [bench' (show n) reduceGF $ linearGraphF n | n <- [12..n]]
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

reduce_linearGraphBigFNE n = bgroup "linearGraphBigFNE"
    [bench' (show n) reduceGF $ linearGraphF n | n <- [10,20..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`

reduce_linearGraphBigFNEST n = bgroup "linearGraphBigFNEST"
    [bench' (show n) reduceGFNEST $ linearGraphFNE n | n <- [10,20..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`



conf name = defaultConfig
    { reportFile      = Just $ "reports/" ++ name ++ ".html"
    , csvFile = Just $ "reports/" ++ name ++ ".csv"
    }



--------------------------------------------------------------------------------
-- * Repmin
--------------------------------------------------------------------------------

repminGFST' :: Free.Graph IntTreeF -> Free.Graph IntTreeF
repminGFST' = snd . Free.runRewriteGraphST const minS minI rep' init
  where init (MinS i) = MinI i

repminGST' :: Graph IntTreeF -> Graph IntTreeF
repminGST' = snd . runRewriteGraphST const minS minI rep' init
  where init (MinS i) = MinI i


repminGFNEST' :: FNE.Graph IntTreeF -> FNE.Graph IntTreeF
repminGFNEST' = snd . FNE.runRewriteGraphST const minS minI rep' init
  where init (MinS i) = MinI i


-- The results for `repmin` are quite consistent with those for `reduce`. One
-- important difference is that `repmin` produces a tree as result, which means
-- that simply forcing a bit result takes some time.

repmin_expTree n = bgroup "expTree"
    [bench' (show n) repmin $ expTree n | n <- [12..n]]
  -- Grows exponentially

repmin_expGraph n = bgroup "expGraph"
    [bench' (show n) repminG $ expGraph n | n <- [12..n]]
  -- Grows exponentially. The overhead compared to `repmin` is about 5x for
  -- trees of size up to 2^16.

repmin_expGraphFST' n = bgroup "expGraphFST'"
    [bench' (show n) repminGFST' $ expGraphF n | n <- [12..n]]

repmin_expGraphFNEST' n = bgroup "expGraphFNEST'"
    [bench' (show n) repminGFNEST' $ expGraphFNE n | n <- [12..n]]


repmin_expGraph' n = bgroup "expGraph'"
    [bench' (show n) repminG' $ expGraph n | n <- [12..n]]
  -- Grows exponentially. The overhead compared to `repmin` is about 70x for
  -- trees of size up to 2^12.

repmin_expGraphST' n = bgroup "expGraphST'"
    [bench' (show n) repminGST' $ expGraph n | n <- [12..n]]

repmin_linearGraph n = bgroup "linearGraph"
    [bench' (show n) repminG $ linearGraph n | n <- [12..n]]

repmin_linearGraph' n = bgroup "linearGraph'"
    [bench' (show n) repminG' $ linearGraph n | n <- [12..n]]
  -- Grows linearly

repmin_linearGraphBig n = bgroup "linearGraphBig"
    [bench' (show n) repminG' $ linearGraph n | n <- [10,20..n]]
  -- Grows linearly even for sizes that are out of reach for `repmin`

repmin_linearGraphBigST n = bgroup "linearGraphBigST"
    [bench' (show n) repminGST' $ linearGraph n | n <- [10,20..n]]


repmin_linearGraphBigFST n = bgroup "linearGraphBigFST"
    [bench' (show n) repminGFST' $ linearGraphF n | n <- [10,20..n]]

repmin_linearGraphBigFNEST n = bgroup "linearGraphBigFNEST"
    [bench' (show n) repminGFNEST' $ linearGraphFNE n | n <- [10,20..n]]


main = do
    defaultMainWith (conf "reduce_overhead_expTree")        [reduce_expTree             16]
    defaultMainWith (conf "reduce_overhead_expGraph")       [reduce_expGraph            16]
    defaultMainWith (conf "reduce_overhead_expGraphST")     [reduce_expGraphST          16]
    defaultMainWith (conf "reduce_overhead_expGraphF")      [reduce_expGraphF           16]
    defaultMainWith (conf "reduce_overhead_expGraphFST")    [reduce_expGraphFST         16]
    defaultMainWith (conf "reduce_overhead_expGraphFNE")    [reduce_expGraphFNE         16]
    defaultMainWith (conf "reduce_overhead_expGraphFNEST")  [reduce_expGraphFNEST       16]
    defaultMainWith (conf "reduce_sharing_expTree")         [reduce_expTree             12]
    defaultMainWith (conf "reduce_sharing_expGraph")        [reduce_expGraph            12]
    defaultMainWith (conf "reduce_sharing_expGraphST")      [reduce_expGraphST          12]
    defaultMainWith (conf "reduce_sharing_expGraphF")       [reduce_expGraphF           12]
    defaultMainWith (conf "reduce_sharing_linearGraph")     [reduce_linearGraph         12]
    defaultMainWith (conf "reduce_sharing_linearGraphF")    [reduce_linearGraphF        12]
    defaultMainWith (conf "reduce_big_linearGraph")         [reduce_linearGraphBig      200]
    defaultMainWith (conf "reduce_big_linearGraphST")       [reduce_linearGraphBigST    200]
    defaultMainWith (conf "reduce_big_linearGraphF")        [reduce_linearGraphBigF     200]
    defaultMainWith (conf "reduce_big_linearGraphFST")      [reduce_linearGraphBigFST   200]
    defaultMainWith (conf "reduce_big_linearGraphFNE")      [reduce_linearGraphBigFNE   200]
    defaultMainWith (conf "reduce_big_linearGraphFNEST")    [reduce_linearGraphBigFNEST 200]

    defaultMainWith (conf "repmin_overhead_expTree")        [repmin_expTree             16]
    defaultMainWith (conf "repmin_overhead_expGraph")       [repmin_expGraph            16]
    defaultMainWith (conf "repmin_overhead_expGraph'")      [repmin_expGraph'           12]  -- OBS only up to 12
    defaultMainWith (conf "repmin_overhead_expGraphST'")    [repmin_expGraphST'         16]
    defaultMainWith (conf "repmin_overhead_expGraphFST'")   [repmin_expGraphFST'        16]
    defaultMainWith (conf "repmin_overhead_expGraphFNEST'") [repmin_expGraphFNEST'      16]
    defaultMainWith (conf "repmin_sharing_expTree")         [repmin_expTree             12]
    defaultMainWith (conf "repmin_sharing_expGraph")        [repmin_expGraph            12]
    defaultMainWith (conf "repmin_sharing_linearGraph")     [repmin_linearGraph         12]
    defaultMainWith (conf "repmin_sharing_linearGraph'")    [repmin_linearGraph         12]
    defaultMainWith (conf "repmin_big_linearGraph")         [repmin_linearGraphBig      200]
    defaultMainWith (conf "repmin_big_linearGraphST")       [repmin_linearGraphBigST    200]
    defaultMainWith (conf "repmin_big_linearGraphFST")      [repmin_linearGraphBigFST   200]
    defaultMainWith (conf "repmin_big_linearGraphFNEST")    [repmin_linearGraphBigFNEST 200]

