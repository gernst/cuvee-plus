// ./Cuvee.sh -known teq -print dfy examples/dafny/parsing/traces_accumulators.dfy
// the syntax of traces with several accumulators (doc/prove.md, section 1.4): the state of the swap
// of two arrays as one trace of three accumulators, read by current(S).i and ⌊S⌋.i; parsed, type-checked and printed
// only (the engine of -prove simplifies such traces, e.g. in examples/dafny/teq/swap.dfy)

lemma exits(a: array<int, int>, b: array<int, int>, n: Nat, S: Trace<(array<int, int>, array<int, int>, int)>)
  requires S == trace(a, b, 0, for ⌊counter(0, 1, n)⌋ do x, y, i, k :: x[i := y[i]], y[i := x[i]], i + 1)
  ensures current(S).2 == integer(n)
  ensures invs(for ⌊counter(0, 1, n)⌋, ⌊S⌋.2 check k, i :: i == k)

lemma guarded(n: Nat, S: Trace<(int, bool)>)
  requires S == trace(0, n == zero, for ⌊counter(0, 1, n)⌋ do x, b, k :: case b => x case !b => x + 1, b)
  ensures current(S).0 == 0 || current(S).0 == integer(n)
