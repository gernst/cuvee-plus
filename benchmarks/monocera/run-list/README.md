Execute `run-list-*` scripts to see their usage.

Currently supports execution of SMT benchmarks, but should be easily extendable for othes. 

Scripts for running [Eldarica](https://github.com/uuverifiers/eldarica) and [Z3](https://github.com/Z3Prover/z3) are provided (binary locations should be updated). 

The produced output log files of various runs can be analyzed by first calling [log2yml](https://github.com/zafer-esen/log2yml) on the outputs to convert them to YAML files, and then calling [yml2stats](https://github.com/zafer-esen/yml2stats) on those files to generate analysis results.
