{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}





import Criterion.Main

import Criterion.Types
import Control.DeepSeq

import AG
import Dag
import Dag.Internal
import Dag.AG
import qualified DagSimple as Simple
import qualified DagSimple.Internal as Simple
import qualified DagSimple.AG as Simple
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

instance NFDataF f => NFData (Dag f)
  where
    rnf (Dag r es n) = rnfF r `seq` rnf n `seq` rnf (fmap rnfF es)


instance NFDataF IntTreeF
  where
    rnfF (Leaf l)   = rnf l `seq` ()
    rnfF (Node a b) = rnf a `seq` rnf b `seq` ()

expTree :: Int -> Tree IntTreeF
expTree 1 = In $ Leaf 10
expTree n = In $ Node (expTree (n-1)) (expTree (n-1))

expSimple :: Int -> Simple.Dag IntTreeF
expSimple = Simple.termTree . expTree

expDag :: Int -> Dag.Dag IntTreeF
expDag = Dag.termTree . expTree

linearSimple :: Int -> Simple.Dag IntTreeF
linearSimple n = Simple.mkDag 0 $
    [(k, Node (k+1) (k+1)) | k <- [0..n-2] ] ++ [(n-1, Leaf 10)]


linearDag :: Int -> Dag.Dag IntTreeF
linearDag n = mkDag (Node (Ret 0) (Ret 0))  $
    [(k, Node (Ret (k+1)) (Ret (k+1))) | k <- [0..n-3] ] ++ [(n-2, Leaf 10)]




--------------------------------------------------------------------------------
-- * Reduce
--------------------------------------------------------------------------------

-- This benchmark is designed to be as simple as possible: only integer
-- attributes and simple semantic functions. This is to make be able to test the
-- efficiency of the run functions themselves.
--
-- The benchmark is run with different AG implementations and dag
-- representations. The names of the benchmarks use "Dag" and "Simple"
-- to indicate that they use the "Dag" and "DagSimple" module,
-- respectively.  The benchmarks mentioned in the paper use the
-- mutable vector implementation.


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

reduceS :: Simple.Dag IntTreeF -> Int
reduceS = fromEnum . Simple.runAGDag max value depth (const 0)

reduceG :: Dag IntTreeF -> Int
reduceG = fromEnum . runAGDag max value depth (const 0)

bench' str f arg = rnf arg `seq` bench str (nf f arg)

reduce_expTree n = bgroup "expTree"
    [bench' (show n) reduce $ expTree n | n <- [startN..n]]
  -- Grows exponentially

reduce_expSimple n = bgroup "expSimple"
    [bench' (show n) reduceS $ expSimple n | n <- [startN..n]]

reduce_expDag n = bgroup "expDag"
    [bench' (show n) reduceG $ expDag n | n <- [startN..n]]


reduce_linearSimple n = bgroup "linearSimple"
    [bench' (show n) reduceS $ linearSimple n | n <- [startN..n]]
  -- Grows linearly

reduce_linearDag n = bgroup "linearDag"
    [bench' (show n) reduceG $ linearDag n | n <- [startN..n]]
  -- Grows linearly

reduce_linearSimpleBig n = bgroup "linearSimpleBig"
    [bench' (show n) reduceS $ linearSimple n | n <- [100,200..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`


reduce_linearDagBig n = bgroup "linearDagBig"
    [bench' (show n) reduceG $ linearDag n | n <- [100,200..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`



conf name = defaultConfig
    { reportFile      = Just $ "reports/" ++ name ++ ".html"
    , csvFile = Just $ "reports/" ++ name ++ ".csv"
    }



--------------------------------------------------------------------------------
-- * Repmin
--------------------------------------------------------------------------------


repminSimple :: Simple.Dag IntTreeF -> Simple.Dag IntTreeF
repminSimple = snd . Simple.runRewriteDag const minS minI rep' init
  where init (MinS i) = MinI i


-- The results for `repmin` are quite consistent with those for `reduce`. One
-- important difference is that `repmin` produces a tree as result, which means
-- that simply forcing a bit result takes some time.

repmin_expTree n = bgroup "expTree"
    [bench' (show n) repmin' $ expTree n | n <- [startN..n]]
  -- Grows exponentially


repmin_expDag n = bgroup "expDag"
    [bench' (show n) repminG' $ expDag n | n <- [startN..n]]

repmin_expSimple n = bgroup "expSimple"
    [bench' (show n) repminSimple $ expSimple n | n <- [startN..n]]

repmin_linearSimple n = bgroup "linearSimple"
    [bench' (show n) repminSimple $ linearSimple n | n <- [startN..n]]


repmin_linearDag n = bgroup "linearDag"
    [bench' (show n) repminG' $ linearDag n | n <- [startN..n]]


repmin_linearSimpleBig n = bgroup "linearSimpleBig"
    [bench' (show n) repminSimple $ linearSimple n | n <- [100,200..n]]


repmin_linearDagBig n = bgroup "linearDagBig"
    [bench' (show n) repminG' $ linearDag n | n <- [100,200..n]]

startN = 4


main = do
    defaultMainWith (conf "reduce_expTree")          [reduce_expTree         16]
    defaultMainWith (conf "reduce_expDag")           [reduce_expDag          16]
    defaultMainWith (conf "reduce_expSimple")        [reduce_expSimple       16]

    defaultMainWith (conf "reduce_linearDag")        [reduce_linearDag       16]
    defaultMainWith (conf "reduce_linearSimple")     [reduce_linearSimple    16]

    defaultMainWith (conf "reduce_big_linearDag")    [reduce_linearDagBig    1000]
    defaultMainWith (conf "reduce_big_linearSimple") [reduce_linearSimpleBig 1000]


    defaultMainWith (conf "repmin_expTree")          [repmin_expTree         16]
    defaultMainWith (conf "repmin_expDag")           [repmin_expDag          16]
    defaultMainWith (conf "repmin_expSimple")        [repmin_expSimple       16]

    defaultMainWith (conf "repmin_linearDag")        [repmin_linearDag       16]
    defaultMainWith (conf "repmin_linearSimple")     [repmin_linearSimple    16]


    defaultMainWith (conf "repmin_big_linearSimple") [repmin_linearSimpleBig 1000]
    defaultMainWith (conf "repmin_big_linearDag")    [repmin_linearDagBig    1000]
