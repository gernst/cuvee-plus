// ./Cuvee.sh -prove examples/dafny/prove/traces_guards.dfy
// cases whose results are equal under a guard are merged: the result of one case, simplified under the guard of the
// other, is the result of that case, so it is the value of both, e.g. j of j != 5 => j is 5 under j == 5 (copysome2-1);
// both results are simplified under the guard, so j + 1 is 6 under j == 5, and c + 1 under j == c; the first is the
// identity map, the next two are true and dropped; the last two keep their cases, since their results differ under the
// guards
type Trace<a₀>
type List<a₀>
const J: List<int>
axiom maps(for J yield j :: case j != 5 => j case j == 5 => 5) == J
axiom maps(for J yield j :: case j == 5 => 6 case j != 5 => j + 1) == maps(for J yield j :: j + 1)
axiom forall c: int :: maps(for J yield j :: case j == c => c + 1 case j != c => j + 1) == maps(for J yield j :: j + 1)
axiom maps(for J yield j :: case j != 5 => j case j == 5 => 6) == J
axiom maps(for J yield j :: case j < 5 => j case 5 <= j => 5) == J
