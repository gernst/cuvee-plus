// ./Cuvee.sh -prove examples/dafny/prove/dependencies.dfy
// the dependencies of combinators: unused ones are dropped, except counters, equal ones are collapsed,
// invariants distribute over conjunctions, each part keeps the dependencies that it uses,
// the iterations of a loop, counted by the first dependency, are 0 <= k < n, and the other dependencies
// have their values in iteration k, also for a variable that denotes the counter by an assumption,
// and the result of a case assumes that the guards of the other cases are false, not so its guard
type Trace<a₀>
type List<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function earlier<a₀>(x₀: int, x₁: List<a₀>): a₀
predicate p(s: List<int>)
const J: List<int>
const K: List<int>
const n: int
const b: bool
const c: bool
axiom p(maps(for K, J yield k, j :: j))
axiom p(maps(for ⌊counter(0, 1, n)⌋, J yield k, j :: j))
axiom invs(for J, J check j, l :: n < j + l)
axiom invs(for K, J check k, j :: 0 < k && 0 < j)
axiom invs(for ⌊counter(0, 1, n)⌋ check k :: 0 <= k)
axiom invs(for ⌊counter(0, 1, n)⌋ check k :: k < n)
axiom invs(for ⌊counter(0, 1, n)⌋, J check k, j :: j == earlier(k, J))
axiom p(maps(for ⌊counter(0, 1, n)⌋, J yield k, j :: case k < n => j case n <= k => 0))
axiom forall I: Trace<int> :: I == counter(0, 1, n) ==> invs(for ⌊I⌋ check k :: k < n)
axiom invs(for J check j :: 0 <= j)
axiom p(maps(for J yield j :: case b => (if c then 1 else j) case c => (if b then 0 else j + 1)))
