{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}





import Criterion.Main

import Criterion.Types
import Control.DeepSeq
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map


import System.IO.Unsafe (unsafePerformIO)

import AG
import Dag
import Dag.Internal
import Dag.AG
import qualified PAG
import qualified Dag.PAG as PAG
import qualified RepminPAG as PAG

import qualified DagSimple as Simple
import qualified DagSimple.Internal as Simple
import qualified DagSimple.AG as Simple
import Paper hiding (Exp(..))
import qualified Feldspar
import Feldspar (Feldspar (..),sizeInfS,sizeInfI,sizeInf,constFoldS,simplifier,simplify,renameFeld)



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

instance NFDataF Feldspar where
  rnfF (Var n) = rnf n `seq` ()
  rnfF (LitB b) = rnf b `seq` ()
  rnfF (LitI i) = rnf i `seq` ()
  rnfF (Add x y) = rnf x `seq` rnf y `seq` ()
  rnfF (Sub x y) = rnf x `seq` rnf y `seq` ()
  rnfF (Mul x y) = rnf x `seq` rnf y `seq` ()
  rnfF (Eq x y) = rnf x `seq` rnf y `seq` ()
  rnfF (Min x y) = rnf x `seq` rnf y `seq` ()
  rnfF (Max x y) = rnf x `seq` rnf y `seq` ()
  rnfF (If x y z) = rnf x `seq` rnf y `seq` rnf z `seq` ()
  rnfF (Let x y z) = rnf x `seq` rnf y `seq` rnf z `seq` ()
  rnfF (Arr x y z) = rnf x `seq` rnf y `seq` rnf z `seq` ()
  rnfF (Ix x y) = rnf x `seq` rnf y `seq` ()

instance NFData Type where
  rnf BoolType = ()
  rnf IntType = ()

instance NFDataF ExpF where
  rnfF (Var' n) = rnf n `seq` ()
  rnfF (LitB' b) = rnf b `seq` ()
  rnfF (LitI' i) = rnf i `seq` ()
  rnfF (Add' x y) = rnf x `seq` rnf y `seq` ()
  rnfF (Eq' x y) = rnf x `seq` rnf y `seq` ()
  rnfF (If' x y z) = rnf x `seq` rnf y `seq` rnf z `seq` ()
  rnfF (Iter' w x y z) = rnf w `seq` rnf x `seq` rnf y `seq` rnf z `seq` ()




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

reduce_expTree n = bgroup "Tree"
    [bench' (show n) reduce $ expTree n | n <- [startN..n]]
  -- Grows exponentially

reduce_expSimple n = bgroup "Simple"
    [bench' (show n) reduceS $ expSimple n | n <- [startN..n]]

reduce_expDag n = bgroup "Dag"
    [bench' (show n) reduceG $ expDag n | n <- [startN..n]]


reduce_linearSimple n = bgroup "Simple"
    [bench' (show n) reduceS $ linearSimple n | n <- [startN..n]]
  -- Grows linearly

reduce_linearDag n = bgroup "Dag"
    [bench' (show n) reduceG $ linearDag n | n <- [startN..n]]
  -- Grows linearly

reduce_linearSimpleBig n = bgroup "Simple"
    [bench' (show n) reduceS $ linearSimple n | n <- [100,200..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`


reduce_linearDagBig n = bgroup "Dag"
    [bench' (show n) reduceG $ linearDag n | n <- [100,200..n]]
  -- Grows linearly even for sizes that are out of reach for `reduce`



conf name = defaultConfig
    { reportFile      = Just $ "reports/" ++ name ++ ".html"
    , csvFile = Just $ "reports/" ++ name ++ ".csv"
    }



--------------------------------------------------------------------------------
-- * Repmin
--------------------------------------------------------------------------------


repminSimple :: Simple.Dag IntTreeF -> Simple.Tree IntTreeF
repminSimple =  snd . Simple.runAGDag const (minS |*| rep) minI init
  where init (MinS i,_) = MinI i


repminSimple' :: Simple.Dag IntTreeF -> Simple.Dag IntTreeF
repminSimple' = snd . Simple.runRewriteDag const minS minI rep' init
  where init (MinS i) = MinI i


-- The results for `repmin` are quite consistent with those for `reduce`. One
-- important difference is that `repmin` produces a tree as result, which means
-- that simply forcing a bit result takes some time.


repmin_expTreeAG n = bgroup "TreeAG"
    [bench' (show n) repmin $ expTree n | n <- [startN..n]]

repmin_expTreePAG n = bgroup "TreePAG"
    [bench' (show n) PAG.repmin $ expTree n | n <- [startN..n]]

repmin_expTree n = bgroup "Tree"
    [bench' (show n) repmin' $ expTree n | n <- [startN..n]]

repmin_expDagAG n = bgroup "DagAG"
    [bench' (show n) repminG $ expDag n | n <- [startN..n]]

repmin_expDagPAG n = bgroup "DagPAG"
    [bench' (show n) PAG.repminG $ expDag n | n <- [startN..n]]

repmin_expDag n = bgroup "Dag"
    [bench' (show n) repminG' $ expDag n | n <- [startN..n]]


repmin_expSimpleAG n = bgroup "SimpleAG"
    [bench' (show n) repminSimple $ expSimple n | n <- [startN..n]]

repmin_expSimple n = bgroup "Simple"
    [bench' (show n) repminSimple' $ expSimple n | n <- [startN..n]]


repmin_linearSimpleAG n = bgroup "SimpleAG"
    [bench' (show n) repminSimple $ linearSimple n | n <- [startN..n]]

repmin_linearSimple n = bgroup "Simple"
    [bench' (show n) repminSimple' $ linearSimple n | n <- [startN..n]]


repmin_linearDagAG n = bgroup "DagAG"
    [bench' (show n) repminG $ linearDag n | n <- [startN..n]]

repmin_linearDagPAG n = bgroup "DagPAG"
    [bench' (show n) PAG.repminG $ linearDag n | n <- [startN..n]]


repmin_linearDag n = bgroup "Dag"
    [bench' (show n) repminG' $ linearDag n | n <- [startN..n]]


repmin_linearSimpleBig n = bgroup "Simple"
    [bench' (show n) repminSimple' $ linearSimple n | n <- [100,200..n]]


repmin_linearDagBig n = bgroup "Dag"
    [bench' (show n) repminG' $ linearDag n | n <- [100,200..n]]


-----------------
-- leavesBelow --
-----------------

leavesBelowSimple :: Int -> Simple.Dag IntTreeF -> Set Int
leavesBelowSimple d = Simple.runAGDag min leavesBelowS leavesBelowI (const d)


leavesBelow_expTree n = bgroup "Tree"
    [bench' (show n) (leavesBelow' 20) $ expTree n | n <- [startN..n]]


leavesBelow_expSimple n = bgroup "Simple"
    [bench' (show n) (leavesBelowSimple 20) $ expSimple n | n <- [startN..n]]

leavesBelow_expDag n = bgroup "Dag"
    [bench' (show n) (leavesBelowG 20) $ expDag n | n <- [startN..n]]


leavesBelow_linearSimple n = bgroup "Simple"
    [bench' (show n) (leavesBelowSimple 20) $ linearSimple n | n <- [startN..n]]


leavesBelow_linearDag n = bgroup "Dag"
    [bench' (show n) (leavesBelowG 20) $ linearDag n | n <- [startN..n]]


leavesBelow_linearSimpleBig n = bgroup "Simple"
    [bench' (show n) (leavesBelowSimple 20) $ linearSimple n | n <- [100,200..n]]


leavesBelow_linearDagBig n = bgroup "Dag"
    [bench' (show n) (leavesBelowG 20) $ linearDag n | n <- [100,200..n]]

-----------------------
-- Feldspar simplify --
-----------------------

simplifySimple :: Simple.Dag Feldspar -> Simple.Dag Feldspar
simplifySimple
    = snd
    . Simple.runRewriteDag
        trueIntersection
        (sizeInfS |*| constFoldS)
        sizeInfI
        simplifier
        (const Map.empty)

simplifyDag :: Dag Feldspar -> Dag Feldspar
simplifyDag
    = snd
    . runRewriteDag
        trueIntersection
        (sizeInfS |*| constFoldS)
        sizeInfI
        simplifier
        (const Map.empty)



exTree :: [Tree Feldspar]
exTree = map Feldspar.unData [Feldspar.ex1, Feldspar.ex2, Feldspar.ex3]

exDag :: [Dag Feldspar]
{-# NOINLINE exDag #-}
exDag = map renameFeld $ unsafePerformIO $ mapM reifyDag exTree

exSimple :: [Simple.Dag Feldspar]
exSimple = map Simple.toSimple exDag

simplify_Tree = bgroup "Tree"
    [bench' (show n) simplify $ exTree !! n | n <- [0..length exTree -1]]

simplify_Dag = bgroup "Dag"
    [bench' (show n) simplifyDag $ exDag !! n | n <- [0..length exDag - 1 ]]

simplify_Simple = bgroup "Simple"
    [bench' (show n) simplifySimple $ exSimple !! n | n <- [0..length exSimple - 1]]


--------------------
-- type inference --
--------------------

typeInfSimple :: Env -> Simple.Dag ExpF -> Maybe Type
typeInfSimple env = Simple.runAGDag trueIntersection typeInfS typeInfI (const env)


exlTree :: [Tree ExpF]
exlTree = [gt1,gt2,gt3]

exlDag :: [Dag ExpF]
{-# NOINLINE exlDag #-}
exlDag = map rename' . unsafePerformIO $ mapM reifyDag exlTree

exlSimple :: [Simple.Dag ExpF]
exlSimple = map Simple.toSimple exlDag

typeInf_Tree = bgroup "Tree"
    [bench' (show n) (typeInf Map.empty) $ exlTree !! n | n <- [0..length exlTree -1]]

typeInf_Dag = bgroup "Dag"
    [bench' (show n) (typeInfG Map.empty) $ exlDag !! n | n <- [0..length exlDag - 1 ]]

typeInf_Simple = bgroup "Simple"
    [bench' (show n) (typeInfSimple Map.empty) $ exlSimple !! n | n <- [0..length exlSimple - 1]]



startN = 4


main = do
    defaultMainWith (conf "reduce_exp")          [reduce_expTree         16
                                                 ,reduce_expDag          16
                                                 ,reduce_expSimple       16]

    defaultMainWith (conf "reduce_linear")        [reduce_linearDag       16
                                                  ,reduce_linearSimple    16]

    defaultMainWith (conf "reduce_big_linear")    [reduce_linearDagBig    1000
                                                  ,reduce_linearSimpleBig 1000]


    defaultMainWith (conf "repmin_exp")          [repmin_expTreeAG       16
                                                 ,repmin_expTreePAG      16
                                                 ,repmin_expTree         16
                                                 ,repmin_expDagAG        16
                                                 ,repmin_expDagPAG       16
                                                 ,repmin_expDag          16
                                                 ,repmin_expSimpleAG     16
                                                 ,repmin_expSimple       16]

    defaultMainWith (conf "repmin_linear")        [repmin_linearDagAG     16
                                                  ,repmin_linearDagPAG    16
                                                  ,repmin_linearDag       16
                                                  ,repmin_linearSimpleAG  16
                                                  ,repmin_linearSimple    16]


    defaultMainWith (conf "repmin_big_linear") [repmin_linearSimpleBig 1000
                                               ,repmin_linearDagBig    1000]


    defaultMainWith (conf "leavesBelow_exp")          [leavesBelow_expTree         16
                                                      ,leavesBelow_expDag          16
                                                      ,leavesBelow_expSimple       16]

    defaultMainWith (conf "leavesBelow_linear")        [leavesBelow_linearDag       16
                                                       ,leavesBelow_linearSimple    16]

    defaultMainWith (conf "leavesBelow_big_linear")    [leavesBelow_linearDagBig    1000
                                                        ,leavesBelow_linearSimpleBig 1000]



    defaultMainWith (conf "simplify")          [simplify_Tree
                                               ,simplify_Dag
                                               ,simplify_Simple]

    defaultMainWith (conf "typeInf")          [typeInf_Tree
                                              ,typeInf_Dag
                                              ,typeInf_Simple]
