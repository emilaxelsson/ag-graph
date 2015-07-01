# Generalising Tree Traversals and Tree Transformations to DAGs


This repository contains the source code associated with the paper
"Generalising Tree Traversals and Tree Transformations to DAGs:
Exploiting Sharing without the Pain" submitted to Science of Computer
Programming.

The technical report containing full proofs of all theorems in the
paper is found [here](docs/tech-report.pdf).

*Note:* the associated material for the PEPM 2015 paper "Generalising
Tree Traversals to DAGs" is found in the
[PEPM branch](https://github.com/emilaxelsson/ag-graph/tree/PEPM).

## File Structure

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
