// the lemma database of -teq, which is injected at the beginning of its output:
// the functions on traces (see cuvee.core.Fun.trace), where butlast is written ⌊X⌋,
// and lemmas about them, which are rewrite rules of the simplifier ({:rw}) and assumed by the solvers ({:free})

// counter(i, c, n) is the trace i, i + c, ..., i + n c of n steps
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
// the last element of a trace
function current<a₀>(x₀: Trace<a₀>): a₀
// the number of steps of a trace, which is one less than the number of its elements
function steps<a₀>(x₀: Trace<a₀>): int
// the length of a sequence
function length<a₀>(x₀: seq<a₀>): int
// the elements of traces and sequences
function nth<a₀>(x₀: int, x₁: Trace<a₀>): a₀
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀

// a variable that is increased by c in each iteration is a counter (example 2.3 of the paper)
lemma {:rw} {:free} forall i: int, c: int, K: Trace<int> ::
  trace(i, for ⌊K⌋ do x, k => x + c) == counter(i, c, steps(K))

// the last element and the number of steps of a counter
lemma {:rw} {:free} forall i: int, c: int, n: int ::
  if 0 <= n then current(counter(i, c, n)) == i + n * c

lemma {:rw} {:free} forall i: int, c: int, n: int ::
  if 0 <= n then steps(counter(i, c, n)) == n

// all but the last element of a trace have the number of its steps
lemma {:rw} {:free} forall X: Trace<int> ::
  length(⌊X⌋) == steps(X)
