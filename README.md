ag-graph
========

Attribute Grammars on Graphs

  * Attribute grammars are defined in module [AG.hs](AG.hs).
  * Graphs and attribute grammars on graphs are defined in module [Graph.hs](Graph.hs).
  * The examples from the paper are in [Paper.hs](Paper.hs).
  * [Bench.hs](Bench.hs) has benchmarks for evaluating the performance.
  * [Rename.hs](Rename.hs) implements a unique renamer for graphs (to ensure well-scopedness before
    running an AG).
  * [Size.hs](Size.hs) implements size inference as an example of an analysis that uses the same
    pattern as type inference in the paper.
