// ./Cuvee.sh -simplify examples/dafny/simplify/traces_sums.dfy
// rewriting of trace equation systems (example 2.6): the dependency V is instantiated by a map over the dependencies
// of the expression, a bound variable that is the value yields the dependency itself,
// and the value must not depend on the accumulator
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function steps(xs: seq<int>): int
predicate p(t: Trace<int>)
const J: Trace<int>
const n: int
function sums(i: int, V: seq<int>): Trace<int>
const W: seq<int>
const arr: array<int, int>
lemma {:rw} forall i: int, V: seq<int> :: trace(i, for V do x, v :: x + v) == sums(i, V)
axiom J == counter(0, 1, n) ==> p(trace(0, for ⌊J⌋ do s, j :: s + arr[j]))
axiom J == counter(0, 1, n) ==> p(trace(0, for ⌊J⌋, W do s, j, w :: w + s))
axiom J == counter(0, 1, n) ==> p(trace(0, for ⌊J⌋ do s, j :: s + s * j))
