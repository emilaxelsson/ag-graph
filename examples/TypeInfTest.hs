-- | Test termination behavior of type inference.
--
-- Conclusion: after renaming, 'typeInfG' gives the same result as 'typeInf'

module TypeInfTest where



import qualified Data.Map as Map

import Dag (unravelDag)
import DagSimple.Internal (mkDag)
import DagSimple (fromSimple)

import TypeInf



exp_fig6b = fromSimple $ mkDag 0
    [ (0, Iter' "x" 1 1 2)
    , (1, LitI' 10)
    , (2, Add' 3 4)
    , (3, Iter' "y" 5 5 6)
    , (4, Var' "x")
    , (5, LitI' 5)
    , (6, Add' 5 4)
    ]

exp3 = fromSimple $ mkDag 0
    [ (0, If' 3 1 2)
    , (1, Iter' "x" 2 2 5)
    , (2, LitI' 10)
    , (3, Iter' "y" 2 4 6)
    , (4, LitB' False)
    , (5, Var' "x")
    , (6, Var' "y")
    ]

exp4 = fromSimple $ mkDag 0
    [ (0, If' 3 1 2)
    , (1, Iter' "x" 2 2 5)
    , (2, LitI' 10)
    , (3, Iter' "x" 2 4 5)
    , (4, LitB' False)
    , (5, Var' "x")
    ]
  -- "x" used at different types

exp5 = fromSimple $ mkDag 0
    [ (0, Iter' "x" 1 2 2)
    , (1, LitI' 10)
    , (2, Var' "x")
    ]
  -- "x" used bound and free

exp6 = fromSimple $ mkDag 0
    [ (0, Iter' "y" 1 1 2)
    , (1, LitI' 0)
    , (2, Iter' "x" 3 3 3)
    , (3, Var' "y")
    ]

exp7 = fromSimple $ mkDag 0
    [ (0, Iter' "x" 1 2 3)
    , (1, LitI' 0)
    , (2, Iter' "x" 1 1 3)
    , (3, Var' "x")
    ]



test_fig6b  = typeInf  Map.empty $ unravelDag exp_fig6b  -- Just
test_fig6bG = typeInfG Map.empty exp_fig6b               -- Just
test_fig6bR = typeInfG Map.empty $ rename' exp_fig6b     -- Just

test3  = typeInf Map.empty $ unravelDag exp3             -- Just
test3G = typeInfG Map.empty exp3                         -- Just
test3R = typeInfG Map.empty $ rename' exp3               -- Just

test4  = typeInf Map.empty $ unravelDag exp4             -- Just
test4G = typeInfG Map.empty exp4                         -- Nothing
test4R = typeInfG Map.empty $ rename' exp4               -- Just

test5  = typeInf Map.empty $ unravelDag exp5             -- Nothing
test5G = typeInfG Map.empty exp5                         -- Nothing
test5R = typeInfG Map.empty $ rename' exp5               -- Nothing

env = Map.fromList [("x", Just IntType)]

test5'  = typeInf env $ unravelDag exp5                  -- Just
test5G' = typeInfG env exp5                              -- loop
test5R' = typeInfG env $ rename' exp5                    -- Just

test6  = typeInf Map.empty $ unravelDag exp6             -- Just
test6G = typeInfG Map.empty exp6                         -- loop
test6R = typeInfG Map.empty $ rename' exp6               -- loop

test7  = typeInf Map.empty $ unravelDag exp7             -- Just
test7G = typeInfG Map.empty exp7                         -- loop
test7R = typeInfG Map.empty $ rename' exp7               -- Just

checkAll
    | allOK     = putStrLn "All tests passed"
    | otherwise = putStrLn "Failed"
  where
    allOK = test_fig6b == test_fig6bR
         && test3      == test3R
         && test4      == test4R
         && test5      == test5R
         && test5'     == test5R'
         && test6      == test6R
         && test7      == test7R

