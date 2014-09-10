Attribute Grammars on Dags
==========================

  * Attribute grammars are defined in module [AG.hs](AG.hs).
  * Dags and attribute grammars on dags are defined in module [Dag.hs](Dag.hs).
  * The simple dag representation is defined in [DagSimple.hs](DagSimple.hs).
  * The examples from the paper are in [Paper.hs](Paper.hs).
  * [Bench.hs](bench/Bench.hs) has benchmarks for evaluating the performance.
  * [Rename.hs](Rename.hs) implements a unique renamer for dags (to ensure well-scopedness before
    running an AG).
  * [Size.hs](Size.hs) implements size inference as an example of an analysis that uses the same
    pattern as type inference in the paper.
