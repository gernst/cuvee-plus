// ./Cuvee.sh -prove examples/dafny/prove/invariants.dfy
// the invariants of the context over some of the dependencies hold in the bodies and updates, not for others,
// and the invariants that mention the combinator itself hold in its update: in X == trace(...), ⌊X⌋ is the accumulator,
// and in Y == maps(...), Y is the update, e.g. the test of a loop lo < hi in the trace of lo, not without the equation
type Trace<a₀>
type List<a₀>
predicate p(s: List<int>)
predicate pt(t: Trace<int>)
const J: List<int>
const K: List<int>
const Y: List<int>
axiom invs(for J check l :: 0 < l) ==> invs(for K, J check k, j :: 0 < j)
axiom invs(for J check l :: 0 < l) ==> p(maps(for J yield j :: case 0 < j => j case j <= 0 => 0))
axiom invs(for J check l :: 0 < l) ==> invs(for K check k :: 0 < k)
axiom forall X: Trace<int> :: invs(for ⌊X⌋, J check x, j :: x < j) ==> X == trace(0, for J do x, j :: if x < j then 1 else 0)
axiom forall X: Trace<int> :: invs(for ⌊X⌋, J check x, j :: x < j) ==> pt(trace(0, for J do x, j :: if x < j then 1 else 0))
axiom invs(for Y, J check y, j :: 0 < j) ==> Y == maps(for J yield j :: if 0 < j then j else -j)
