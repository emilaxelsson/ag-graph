# Generalising Tree Traversals to DAGs


This repository contains the source code associated with the paper
["Generalising Tree Traversals to DAGs: Exploiting Sharing without the Pain" (PEPM 2015)](http://dx.doi.org/10.1145/2678015.2682539).

The revised and extended implementation associated with the paper
"Generalising Tree Traversals and Tree Transformations to DAGs"
(submitted to Science of Computer Programming) is found in the
[main branch](https://github.com/emilaxelsson/ag-graph).

## File Structure

  * Attribute grammars are defined in module [AG.hs](AG.hs).
  * DAGs and attribute grammars on DAGs are defined in module [Dag.hs](Dag.hs).
  * The simple DAG representation is defined in [DagSimple.hs](DagSimple.hs).
  * The examples from the paper are in [Paper.hs](Paper.hs).
  * [Bench.hs](bench/Bench.hs) has benchmarks for evaluating the performance.
  * [Rename.hs](Rename.hs) implements a unique renamer for DAGs (to ensure well-scopedness before
    running an AG).
  * [Size.hs](Size.hs) implements size inference as an example of an analysis that uses the same
    pattern as type inference in the paper.
