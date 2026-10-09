// ./Cuvee.sh -simplify examples/dafny/simplify/traces_higher_order.dfy
// higher-order patterns P(x) of variables of function type applied to bound variables (Miller's fragment), where the
// dependency Xs follows from the bound variable of the expression, the instantiated right-hand side is beta-reduced,
// a single bound variable of the pattern cannot abstract two of the expression, repeated occurrences must agree,
// and the accumulator may be abstracted as well
type Trace<a₀>
type List<a₀>
type Nat
function counter(x₀: int, x₁: int, x₂: Nat): Trace<int>
function steps(xs: List<int>): int
predicate p(t: Trace<int>)
const J: Trace<int>
const n: int
const W: List<int>
const done: bool
predicate r(x: int, y: int)
predicate either(a: bool, b: bool)
function fold(i: int, xs: List<int>, f: (int, int) -> int): Trace<int>
lemma {:rw} invs_1(Xs: List<int>, P: int -> bool, Q: int -> bool)
  ensures invs(for Xs check x :: P(x) || Q(x)) == either(invs(for Xs check x :: P(x)), invs(for Xs check x :: Q(x)))
{}
lemma {:rw} invs_2(Xs: List<int>, F: int -> int)
  ensures invs(for Xs check x :: r(F(x), F(x))) == done
{}
lemma {:rw} trace_1(i: int, Xs: List<int>, F: (int, int) -> int)
  ensures trace(i, for Xs do x, v :: F(x, v)) == fold(i, Xs, F)
{}
axiom invs(for ⌊J⌋ check j :: j < n || 0 <= j)
axiom invs(for ⌊J⌋, W check j, w :: j < n || w < j)
axiom invs(for ⌊J⌋ check j :: r(j + 1, j + 1))
axiom invs(for ⌊J⌋ check j :: r(j + 1, j + 2))
axiom p(trace(0, for ⌊J⌋ do s, j :: s * j + 1))
