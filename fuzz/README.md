# The harness of the fuzzer of portfolio.py

Copied from Korn (../korn, MIT License, Copyright (c) 2020 Gidon Ernst), unchanged:

- `__VERIFIER.c`: the functions `__VERIFIER_nondet_*` of SV-COMP, each through `__VERIFIER_next_nondet`.
- `__VERIFIER_random.c`: `__VERIFIER_next_nondet` draws small values around 0 and records them; `reach_error`
  (`__assert_fail`) prints `unsat`, the recorded values and the seed; a run ends after one second.
