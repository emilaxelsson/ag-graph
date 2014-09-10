{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}





import Criterion.Main

import Criterion.Types
import Control.DeepSeq

import AG
import qualified DagSimple as Simple
import qualified DagFree as Free
import qualified Dag as Dag
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


instance NFDataF f => NFData (Simple.Dag f)
  where
    rnf (Simple.Dag r es n) = rnf r `seq` rnf n `seq` rnf (fmap rnfF es)

instance NFDataF f => NFData (Dag.Dag f)
  where
    rnf (Dag.Dag r es n) = rnfF r `seq` rnf n `seq` rnf (fmap rnfF es)


instance NFDataF IntTreeF
  where
    rnfF (Leaf l)   = rnf l `seq` ()
    rnfF (Node a b) = rnf a `seq` rnf b `seq` ()

expTree :: Int -> Tree IntTreeF
expTree 1 = In $ Leaf 10
expTree n = In $ Node (expTree (n-1)) (expTree (n-1))

expSimple :: Int -> Simple.Dag IntTreeF
expSimple = Simple.termTree . expTree

expFree :: Int -> Free.Dag IntTreeF
expFree = Free.termTree . expTree

expDag :: Int -> Dag.Dag IntTreeF
expDag = Dag.termTree . expTree

linearSimple :: Int -> Simple.Dag IntTreeF
linearSimple n = Simple.mkDag 0 $
    [(k, Node (k+1) (k+1)) | k <- [0..n-2] ] ++ [(n-1, Leaf 10)]

linearFree :: Int -> Free.Dag IntTreeF
linearFree n = Simple.mkDag 0 $
    [(k, In $ Node (Ret (k+1)) (Ret (k+1))) | k <- [0..n-2] ] ++ [(n-1, In (Leaf 10))]

linearDag :: Int -> Dag.Dag IntTreeF
linearDag n = Dag.mkDag (Node (Ret 0) (Ret 0))  $
    [(k, Node (Ret (k+1)) (Ret (k+1))) | k <- [0..n-3] ] ++ [(n-2, Leaf 10)]




--------------------------------------------------------------------------------
-- * Reduce
--------------------------------------------------------------------------------

-- This benchmark is designed to be as simple as possible: only integer
-- attributes and simple semantic functions. This is to make be able to test the
-- efficiency of the run functions themselves.
--
-- The benchmark is run with different AG implementations and dag
-- representations. The names of the benchmarks use "Dag", "Free" and
-- "Simple" to indicate that they use the "Dag", "DagFree" and
-- "DagSimple" module, respectively. The suffix "ST" indicates that
-- the mutable vector implementation is used. The benchmarks mentioned
-- in the paper use the mutable vector implementation.


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
reduce = fromEnum . runAG value depth (const 0)

reduceGS :: Simple.Dag IntTreeF -> Int
reduceGS = fromEnum . Simple.runAGDag max value depth (const 0)

reduceGSST :: Simple.Dag IntTreeF -> Int
reduceGSST = fromEnum . Simple.runAGDagST max value depth (const 0)


reduceGF :: Free.Dag IntTreeF -> Int
reduceGF = fromEnum . Free.runAGDag max value depth (const 0)

reduceGFST :: Free.Dag IntTreeF -> Int
reduceGFST = fromEnum . Free.runAGDagST max value depth (const 0)


reduceG :: Dag.Dag IntTreeF -> Int
reduceG = fromEnum . Dag.runAGDag max value depth (const 0)

reduceGST :: Dag.Dag IntTreeF -> Int
reduceGST = fromEnum . Dag.runAGDagST max value depth (const 0)

bench' str f arg = rnf arg `seq` bench str (nf f arg)

reduce_expTree n = bgroup "expTree"
    [bench' (show n) reduce $ expTree n | n <- [startN..n]]
  -- Grows exponentially

reduce_expSimple n = bgroup "expSimple"
    [bench' (show n) reduceGS $ expSimple n | n <- [startN..n]]

reduce_expSimpleST n = bgroup "expSimpleST"
    [bench' (show n) reduceGSST $ expSimple n | n <- [startN..n]]

reduce_expFree n = bgroup "expFree"
    [bench' (show n) reduceGF $ expFree n | n <- [startN..n]]

reduce_expDag n = bgroup "expDag"
    [bench' (show n) reduceG $ expDag n | n <- [startN..n]]


reduce_expFreeST n = bgroup "expFreeST"
    [bench' (show n) reduceGFST $ expFree n | n <- [startN..n]]

reduce_expDagST n = bgroup "expDagST"
    [bench' (show n) reduceGST $ expDag n | n <- [startN..n]]


reduce_linearSimple n = bgroup "linearSimple"
    [bench' (show n) reduceGS $ linearSimple n | n <- [startN..n]]
  -- Grows linearly

reduce_linearSimpleST n = bgroup "linearSimpleST"
    [bench' (show n) reduceGSST $ linearSimple n | n <- [startN..n]]
  -- Grows linearly


reduce_linearFree n = bgroup "linearFree"
    [bench' (show n) reduceGF $ linearFree n | n <- [startN..n]]
  -- Grows linearly

reduce_linearFreeST n = bgroup "linearFreeST"
    [bench' (show n) reduceGFST $ linearFree n | n <- [startN..n]]
  -- Grows linearly

reduce_linearDag n = bgroup "linearDag"
    [bench' (show n) reduceG $ linearDag n | n <- [startN..n]]
  -- Grows linearly

reduce_linearDagST n = bgroup "linearDagST"
    [bench' (show n) reduceGST $ linearDag n | n <- [startN..n]]
  -- Grows linearly


reduce_linearSimpleBig n = bgroup "linearSimpleBig"
    [bench' (show n) reduceGS $ linearSimple n | n <- [100,200..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`

reduce_linearSimpleBigST n = bgroup "linearSimpleBigST"
    [bench' (show n) reduceGSST $ linearSimple n | n <- [100,200..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`


reduce_linearFreeBig n = bgroup "linearFreeBig"
    [bench' (show n) reduceGF $ linearFree n | n <- [100,200..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`

reduce_linearFreeBigST n = bgroup "linearFreeBigST"
    [bench' (show n) reduceGFST $ linearFree n | n <- [100,200..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`

reduce_linearDagBig n = bgroup "linearDagBig"
    [bench' (show n) reduceGF $ linearFree n | n <- [100,200..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`

reduce_linearDagBigST n = bgroup "linearDagBigST"
    [bench' (show n) reduceGST $ linearDag n | n <- [100,200..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`



conf name = defaultConfig
    { reportFile      = Just $ "reports/" ++ name ++ ".html"
    , csvFile = Just $ "reports/" ++ name ++ ".csv"
    }



--------------------------------------------------------------------------------
-- * Repmin
--------------------------------------------------------------------------------

repminFreeST :: Free.Dag IntTreeF -> Free.Dag IntTreeF
repminFreeST = snd . Free.runRewriteDagST const minS minI rep' init
  where init (MinS i) = MinI i


repminSimpleST :: Simple.Dag IntTreeF -> Simple.Dag IntTreeF
repminSimpleST = snd . Simple.runRewriteDagST const minS minI rep' init
  where init (MinS i) = MinI i

repminSimple :: Simple.Dag IntTreeF -> Simple.Dag IntTreeF
repminSimple = snd . Simple.runRewriteDag const minS minI rep' init
  where init (MinS i) = MinI i


repminGST :: Dag.Dag IntTreeF -> Dag.Dag IntTreeF
repminGST = snd . Dag.runRewriteDagST const minS minI rep' init
  where init (MinS i) = MinI i


-- The results for `repmin` are quite consistent with those for `reduce`. One
-- important difference is that `repmin` produces a tree as result, which means
-- that simply forcing a bit result takes some time.

repmin_expTree n = bgroup "expTree"
    [bench' (show n) repmin $ expTree n | n <- [startN..n]]
  -- Grows exponentially


repmin_expFreeST n = bgroup "expFreeST"
    [bench' (show n) repminFreeST $ expFree n | n <- [startN..n]]

repmin_expDagST n = bgroup "expDagST"
    [bench' (show n) repminGST $ expDag n | n <- [startN..n]]

repmin_expSimple n = bgroup "expSimple"
    [bench' (show n) repminSimple $ expSimple n | n <- [startN..n]]

repmin_expSimpleST n = bgroup "expSimpleST"
    [bench' (show n) repminSimpleST $ expSimple n | n <- [startN..n]]


repmin_linearSimple n = bgroup "linearSimple"
    [bench' (show n) repminSimple $ linearSimple n | n <- [startN..n]]


repmin_linearSimpleST n = bgroup "linearSimpleST"
    [bench' (show n) repminSimpleST $ linearSimple n | n <- [startN..n]]


repmin_linearFreeST n = bgroup "linearFreeST"
    [bench' (show n) repminFreeST $ linearFree n | n <- [startN..n]]

repmin_linearDagST n = bgroup "linearDagST"
    [bench' (show n) repminGST $ linearDag n | n <- [startN..n]]


repmin_linearSimpleBig n = bgroup "linearSimpleBig"
    [bench' (show n) repminSimple $ linearSimple n | n <- [100,200..n]]


repmin_linearSimpleBigST n = bgroup "linearSimpleBigST"
    [bench' (show n) repminSimpleST $ linearSimple n | n <- [100,200..n]]


repmin_linearFreeBigST n = bgroup "linearFreeBigST"
    [bench' (show n) repminFreeST $ linearFree n | n <- [100,200..n]]

repmin_linearDagBigST n = bgroup "linearDagBigST"
    [bench' (show n) repminGST $ linearDag n | n <- [100,200..n]]

startN = 4


main = do

    -- all benchmarks --
 
    -- defaultMainWith (conf "reduce_expTree")            [reduce_expTree           16]
    -- defaultMainWith (conf "reduce_expSimple")          [reduce_expSimple         16]
    -- defaultMainWith (conf "reduce_expSimpleST")        [reduce_expSimpleST       16]
    -- defaultMainWith (conf "reduce_expFree")            [reduce_expFree           16]
    -- defaultMainWith (conf "reduce_expFreeST")          [reduce_expFreeST         16]
    -- defaultMainWith (conf "reduce_expDag")             [reduce_expDag            16]
    -- defaultMainWith (conf "reduce_expDagST")           [reduce_expDagST          16]

    -- defaultMainWith (conf "reduce_linearSimple")       [reduce_linearSimple      16]
    -- defaultMainWith (conf "reduce_linearSimpleST")     [reduce_linearSimpleST    16]
    -- defaultMainWith (conf "reduce_linearFree")         [reduce_linearFree        16]
    -- defaultMainWith (conf "reduce_linearFreeST")       [reduce_linearFreeST      16]
    -- defaultMainWith (conf "reduce_linearDag")          [reduce_linearDag         16]
    -- defaultMainWith (conf "reduce_linearDagST")        [reduce_linearDagST       16]

    -- defaultMainWith (conf "reduce_big_linearSimple")   [reduce_linearSimpleBig     1000]
    -- defaultMainWith (conf "reduce_big_linearSimpleST") [reduce_linearSimpleBigST   1000]
    -- defaultMainWith (conf "reduce_big_linearFree")     [reduce_linearFreeBig     1000]
    -- defaultMainWith (conf "reduce_big_linearFreeST")   [reduce_linearFreeBigST   1000]
    -- defaultMainWith (conf "reduce_big_linearDag")      [reduce_linearDagBig      1000]
    -- defaultMainWith (conf "reduce_big_linearDagST")    [reduce_linearDagBigST    1000]

    -- defaultMainWith (conf "repmin_expTree")            [repmin_expTree           16]
    -- defaultMainWith (conf "repmin_expSimple")          [repmin_expSimple         12]  -- OBS only up to 12
    -- defaultMainWith (conf "repmin_expSimpleST")        [repmin_expSimpleST       12]
    -- defaultMainWith (conf "repmin_expFreeST")          [repmin_expFreeST         16]
    -- defaultMainWith (conf "repmin_expDagST")           [repmin_expDagST          16]

    -- defaultMainWith (conf "repmin_linearSimple")       [repmin_linearSimple      16]
    -- defaultMainWith (conf "repmin_linearSimpleST")     [repmin_linearSimpleST    16]
    -- defaultMainWith (conf "repmin_linearFreeST")       [repmin_linearFreeST      16]
    -- defaultMainWith (conf "repmin_linearDagST")        [repmin_linearDagST       16]

    -- defaultMainWith (conf "repmin_big_linearSimple")   [repmin_linearSimpleBig   1000]
    -- defaultMainWith (conf "repmin_big_linearSimpleST") [repmin_linearSimpleBigST 1000]
    -- defaultMainWith (conf "repmin_big_linearFreeST")   [repmin_linearFreeBigST   1000]
    -- defaultMainWith (conf "repmin_big_linearDagST")    [repmin_linearDagBigST    1000]


    -- benchmarks from the paper --

    defaultMainWith (conf "reduce_expTree")            [reduce_expTree           16]
    defaultMainWith (conf "reduce_expDagST")           [reduce_expDagST          16]
    defaultMainWith (conf "reduce_linearDagST")        [reduce_linearDagST       16]

    defaultMainWith (conf "reduce_expSimple")          [reduce_expSimple         16]
    defaultMainWith (conf "reduce_linearSimple")       [reduce_linearSimple      16]

    defaultMainWith (conf "reduce_big_linearSimpleST") [reduce_linearSimpleBigST 1000]
    defaultMainWith (conf "reduce_big_linearDagST")    [reduce_linearDagBigST    1000]


    defaultMainWith (conf "repmin_expTree")            [repmin_expTree           16]
    defaultMainWith (conf "repmin_expSimpleST")        [repmin_expSimpleST       16]
    defaultMainWith (conf "repmin_expDagST")           [repmin_expDagST          16]

    defaultMainWith (conf "repmin_linearSimpleST")     [repmin_linearSimpleST    16]
    defaultMainWith (conf "repmin_linearDagST")        [repmin_linearDagST       16]

    defaultMainWith (conf "repmin_big_linearSimpleST") [repmin_linearSimpleBigST 1000]
    defaultMainWith (conf "repmin_big_linearDagST")    [repmin_linearDagBigST    1000]
