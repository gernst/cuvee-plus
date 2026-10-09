// ./Cuvee.sh -teq -simplify examples/sv-comp/array-crafted/mapsum1.dfy
// SV-COMP ReachSafety-Arrays/array-crafted/mapsum1.yml (expected: safe), translated from the C program by hand:
// the sum of i + x[i] over an arbitrary array of N = 100 elements (the function mapsum, inlined at its three
// calls) does not change when x[0] and x[1] are swapped, and when the array is then rotated by one position
//
// findings: the representative of the 25 tasks that check a fold over an array of 100 elements (mapsum, mapavg,
// bAnd, bor, xor, the latter three bitwise, which the Dafny frontend does not parse) for invariance under a swap of
// x[0] and x[1] and a rotation by one; -teq resolves the swap, and the rotation is a loop summarized as shifts; a
// lemma states the sum after shifting by one; open: the remaining equations differ only in ⌊K₃₇⌋ and ⌊counter(0, 1,
// 100)⌋, or ⌊I₁₉⌋, which the definitions of the context make equal, while expressions are compared literally; the
// lemma variant that keeps the matched positions ks on its right-hand side, with the side condition ks ==
// ⌊counter(0, 1, m + 1)⌋, does not apply, since that side condition is not decided (see TODO.md)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function shifts(a: array<int, int>, keys: seq<int>, d: int): Trace<array<int, int>>
function selects<a, b>(a: array<a, b>, keys: seq<a>): seq<b>
function sum(values: seq<int>): int

// shifting the elements at the positions 1, ..., m down by one keeps the element at m, hence the sum over the
// positions 0, ..., m loses a[0] and counts a[m] twice
lemma {:rw} {:free} {:teq} forall a: array<int, int>, m: int, n: int ::
  if 0 <= m && n == m + 1
  then sum(selects(current(shifts(a, ⌊counter(0, 1, m)⌋, 1)), ⌊counter(0, 1, n)⌋))
    == sum(selects(a, ⌊counter(0, 1, n)⌋)) - a[0] + a[m]

method main() {
  var N: int;
  var i: int;
  var v: int;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var x: array<int, int>;
  N := 100;
  i := 0;
  while i < N {
    v := *;
    x := x[i := v];
    i := i + 1;
  }
  ret := 0;
  i := 0;
  while i < N {
    ret := ret + i + x[i];
    i := i + 1;
  }
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  ret2 := 0;
  i := 0;
  while i < N {
    ret2 := ret2 + i + x[i];
    i := i + 1;
  }
  temp := x[0];
  i := 0;
  while i < N - 1 {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[N - 1 := temp];
  ret5 := 0;
  i := 0;
  while i < N {
    ret5 := ret5 + i + x[i];
    i := i + 1;
  }
  assert ret == ret2 && ret == ret5;
}

// remaining goals of -teq -simplify:
// goal
//   forall x₈: array<int, int>, x₂₁: array<int, int>, X₁₈: Trace<array<int, int>>,
//          I₁₉: Trace<int>, V?₁₃: seq<int>, K₃₇: Trace<int> ::
//     x₂₁ == current(X₁₈)
//       && X₁₈ == stores(x₈, ⌊I₁₉⌋, V?₁₃)
//       && I₁₉ == counter(0, 1, 100)
//       && K₃₇ == counter(0, 1, 100)
//       ==> sum(selects(x₂₁, ⌊counter(0, 1, 100)⌋)) == sum(selects(x₂₁, ⌊K₃₇⌋))
//         && sum(V?₁₃) == sum(selects(x₂₁, ⌊counter(0, 1, 100)⌋))
