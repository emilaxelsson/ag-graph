Attribute Grammars on DAGs
==========================

  * The library implementation is in the [src](src) subdirectory.
  * (Parametric) attribute grammars on trees are defined in the
    modules [AG](src/AG.hs) and [PAG](src/PAG.hs).
  * (Parametric) attribute grammars on DAGs are defined in the modules
    [Dag.AG](src/Dag/AG.hs) and [Dag.PAG](src/Dag/PAG.hs).
  * [bench/Bench.hs](bench/Bench.hs) has benchmarks for evaluating the
    performance.
  * Use the command `cabal bench` to run the benchmarks. The benchmark
    reports are written into the `reports` subdirectory.
  * Examples from the paper can be found in the [examples](examples) subdirectory.
