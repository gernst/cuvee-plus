// ./Cuvee.sh -prove examples/dafny/simplify/traces_all.dfy
// all(for ⌊K⌋ check k :: k < len) with the bound variable related to that of the expression,
// and the variables of the rule must not capture the bound variables of the expression
type Trace<a₀>
type List<a₀>
type Nat
function counter(x₀: int, x₁: int, x₂: Nat): Trace<int>
function steps(xs: List<int>): int
predicate p(t: Trace<int>)
const J: Trace<int>
const n: int
predicate r(x: int, y: int)
predicate le(x: int, y: int)
lemma {:rw} invs_1(len: int, K: Trace<int>)
  ensures invs(for ⌊K⌋ check k :: k < len) == le(steps(⌊K⌋), len)
{}
lemma {:rw} invs_2(c: int, K: Trace<int>)
  ensures invs(for ⌊K⌋ check k :: r(c, k)) == true
{}
axiom invs(for ⌊J⌋ check j :: j < n)
axiom invs(for ⌊J⌋ check j :: r(j, j))
