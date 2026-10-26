// ./Cuvee.sh -print lean examples/dafny/printing/lean_accumulators.dfy
// traces of several accumulators in Lean: a trace of the product of the accumulators, whose initial value and
// results are tuples and whose accumulators are bound by ⟨x, b⟩, the components current(S).i selected from the
// nested pairs, and the histories ⌊S⌋.i as the list of a component of the earlier values; the declarations of teq.dfy
// that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
type {:lean} List<a₀>
type {:lean} int
function butlast<a₀>(x₀: Trace<a₀>): List<a₀>
function current<a₀>(x₀: Trace<a₀>): a₀

lemma flag(K: List<int>, S: Trace<(int, bool)>)
  requires S == trace(0, true, for K do x, b, k :: case b => x + k case !b => x, !b)
  ensures invs(for K, ⌊S⌋.0, ⌊S⌋.1 check k, y, c :: c || 0 <= y) ==> 0 <= current(S).0

lemma three(K: List<int>, S: Trace<(int, int, int)>)
  requires S == trace(0, 1, 2, for K do x, y, z, k :: y, z, x + k)
  ensures current(S).0 + current(S).1 + current(S).2 == current(S).2 + current(S).1 + current(S).0
