Attribute Grammars on DAGs
==========================

  * The library implementation is in the [src](src) subdirectory.
  * (Parametric) attribute grammars on trees are defined in the
    modules [AG](src/AG.hs) and [PAG](src/PAG.hs).
  * (Parametric) attribute grammars on DAGs are defined in the modules
    [Dag.AG](src/Dag/AG.hs) and [Dag.PAG](src/Dag/PAG.hs).
  * [bench/Bench.hs](bench/Bench.hs) has benchmarks for evaluating the performance.
  * Examples can be found in the [examples](examples) subdirectory:
    - the examples from the paper are in
      [Paper.hs](examples/Paper.hs).
    - [Rename.hs](examples/Rename.hs) implements a unique renamer for
      dags (to ensure well-scopedness before running an AG).
    - [Size.hs](examples/Size.hs) implements size inference as an
      example of an analysis that uses the same pattern as type
      inference in the paper.
