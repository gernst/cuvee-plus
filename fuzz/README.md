# The harness of the fuzzer of portfolio.py

Copied from Korn (../korn, MIT License, Copyright (c) 2020 Gidon Ernst); changed only in the ranges of the values:

- `__VERIFIER.c`: the functions `__VERIFIER_nondet_*` of SV-COMP, each through `__VERIFIER_next_nondet`.
- `__VERIFIER_random.c`: `__VERIFIER_next_nondet` draws small values around 0 and records them; `reach_error`
  (`__assert_fail`) prints `unsat`, the recorded values and the seed; a run ends after one second. The values are
  drawn from six cases alike: 0, 0..1, -3..4, -15..16, -511..512, -32767..32768 (unsigned 0, 0..1, 0..7, 0..31,
  0..1023, 0..65535); Korn's ranges, -1..0, -16..15, -512..511, never drew 1 from the narrowest one, which
  array-tiling/skippedu needs exactly (Oct 31, 2026: the fuzzer finds 38 of the 39 false tasks of Arrays and Loops
  that -chc proves and -teq -fallback does not, 10 s each; the last one, simple_array_index_value_1-2, is false
  only by an uninitialized local array).
