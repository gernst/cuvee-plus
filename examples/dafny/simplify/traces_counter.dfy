// ./Cuvee.sh -simplify examples/dafny/simplify/traces_counter.dfy
// rewriting of trace equation systems (example 2.3): a variable increased by c in each iteration is a counter,
// matched modulo commutativity, every case of the update is covered by the case of the pattern,
// different increments in the cases are not a counter
type Trace<a₀>
type List<a₀>
type Nat
function counter(x₀: int, x₁: int, x₂: Nat): Trace<int>
function steps(xs: List<int>): Nat
predicate p(t: Trace<int>)
const J: Trace<int>
const n: Nat
lemma {:rw} trace_1(i: int, c: int, K: Trace<int>)
  ensures trace(i, for ⌊K⌋ do x, k :: x + c) == counter(i, c, steps(⌊K⌋))
{}
axiom p(trace(0, for ⌊J⌋ do s, j :: 1 + s))
axiom J == counter(0, 1, n) ==> p(trace(0, for ⌊J⌋ do s, j :: case j < 5 => s + 1 case !(j < 5) => s + 1))
axiom J == counter(0, 1, n) ==> p(trace(0, for ⌊J⌋ do s, j :: case j < 5 => s + 1 case !(j < 5) => s + 2))
