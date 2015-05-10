--------------------------------------------------------------------------------
-- |
-- Module      :  Dag.Internal
-- Copyright   :  (c) 2014 Patrick Bahr, Emil Axelsson
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@di.ku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the types for representing DAGs. However,
-- 'Dag's should only be constructed using the interface provided by
-- "Dag".
--
--------------------------------------------------------------------------------

module Dag.Internal where

import Tree
import Data.IntMap (IntMap)

-- | The type of node in a 'Dag'.

type Node = Int

-- | The type of the compact edge representation used in a 'Dag'.

type Edges f = IntMap (f (Free f Node))

-- | The type of directed acyclic graphs (DAGs). 'Dag's are used as a
-- compact representation of 'Term's.

data Dag f = Dag 
    { root      :: f (Free f Node) -- ^ the entry point for the DAG
    , edges     :: Edges f         -- ^ the edges of the DAG
    , nodeCount :: Int             -- ^ the total number of nodes in the DAG
    }
