// ./Cuvee.sh -print lean examples/dafny/printing/lean_teq.dfy
// the combinators of trace equation systems in Lean, applications of the functions of lean/TEQ/Semantics.lean by
// the number of their dependencies to the update as a function of the bound variables, guarded cases as
// conditionals; the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
type {:lean} List<a₀>
type {:lean} int
function butlast<a₀>(x₀: Trace<a₀>): List<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

lemma {:rw} capped(x0: int, n: int, b: int, hs: List<int>)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do x, k, h :: case x < b => x + h case b <= x => x))
    == current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do x, k, h :: if x < b then x + h else x))

lemma {:rw} bounded(n: int, xs: List<int>, b: int)
  requires invs(for xs check x :: x <= b)
  ensures maps(for ⌊counter(0, 1, n)⌋ yield k :: k + 1) == maps(for ⌊counter(1, 1, n)⌋ yield k :: k)
