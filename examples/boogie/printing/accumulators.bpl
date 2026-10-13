// ./Cuvee.sh -print smt2 examples/boogie/printing/accumulators.bpl
// traces of several accumulators in Boogie, as in Dafny: the initial values, the accumulators before the bound
// variables, one result each, and the components current(S).i and histories ⌊S⌋.i, with the declarations of teq.dfy
// that they need, and the tuple of the state
data tuple₂<a₀, a₁> = tuple₂(tuple₂_0: a₀, tuple₂_1: a₁);

type Trace<a₀>;

type List<a₀>;

function butlast<a₀>(x₀: Trace<a₀>): List<a₀>;

function current<a₀>(x₀: Trace<a₀>): a₀;

function swap(K: List<int>, S: Trace<tuple₂<int, bool>>): bool {
  S == trace(0, true, for K do x, b, k :: case b => x + k case !b => x, !b)
    ==> 0 <= current(S).0
      && all(for K, ⌊S⌋.0, ⌊S⌋.1 check k, y, c :: c || 0 <= y)
}
