// ./Cuvee.sh -simplify examples/dafny/simplify/traces_sums.dfy
// rewriting of trace equation systems (example 2.6): the dependency V is instantiated by a map over the dependencies
// of the expression, a bound variable that is the value yields the dependency itself,
// and the value must not depend on the accumulator
type Trace<a₀>
type List<a₀>
type Nat
function counter(x₀: int, x₁: int, x₂: Nat): Trace<int>
function steps(xs: List<int>): Nat
predicate p(t: Trace<int>)
const J: Trace<int>
const n: Nat
function sums(i: int, V: List<int>): Trace<int>
const W: List<int>
const arr: array<int, int>
lemma {:rw} trace_1(i: int, V: List<int>)
  ensures trace(i, for V do x, v :: x + v) == sums(i, V)
{}
axiom J == counter(0, 1, n) ==> p(trace(0, for ⌊J⌋ do s, j :: s + arr[j]))
axiom J == counter(0, 1, n) ==> p(trace(0, for ⌊J⌋, W do s, j, w :: w + s))
axiom J == counter(0, 1, n) ==> p(trace(0, for ⌊J⌋ do s, j :: s + s * j))
