// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/standard_vararg_ground.dfy
// SV-COMP array-examples/standard_vararg_ground.yml (expected: safe), translated from the C program by hand:
// a counts the leading nonnegative elements of an arbitrary array (the C program reads beyond the array if all
// are nonnegative), and they are checked to be nonnegative
//
// findings: the loop runs while the elements are nonnegative, also beyond the array, whose reads are then of the
// initial array; open: the goal is the iteration constraint over n₂₂ iterations instantiated at n₂₈ < n₂₂, with the
// body 0 <= (if k < 100000 then earlier(k, V?) else aa[k]), which needs an instantiation of an iteration constraint
// with an arbitrary body, which the lemmas abstract by atoms for specific bodies only; no lemmas tried
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var a: int;
  var x: int;
  var v: int;
  var aa: array<int, int>;
  assume 0 < N;
  a := 0;
  i := 0;
  while i < N {
    v := *;
    aa := aa[i := v];
    i := i + 1;
  }
  while aa[a] >= 0 {
    a := a + 1;
  }
  x := 0;
  while x < a {
    assert aa[x] >= 0;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// goal
//   forall aa₅: array<int, int>, V?₁₀: seq<int>, n₂₂: int, K₂₄: Trace<int>,
//          A₂₅: Trace<int>, n₂₈: int, K₃₀: Trace<int>, X₃₁: Trace<int> ::
//     K₂₄ == counter(0, 1, n₂₂)
//       && A₂₅ == counter(0, 1, n₂₂)
//       && invs(for ⌊K₂₄⌋, ⌊A₂₅⌋
//               check k₂₃, a₂₁ ::
//                 0 <= (if k₂₃ < 100000 then earlier(k₂₃, V?₁₀) else aa₅[k₂₃]))
//       && (if n₂₂ < 100000 then earlier(n₂₂, V?₁₀) else aa₅[n₂₂]) < 0
//       && K₃₀ == counter(0, 1, n₂₈)
//       && X₃₁ == counter(0, 1, n₂₈)
//       && invs(for ⌊K₃₀⌋, ⌊X₃₁⌋
//               check k₂₉, x₂₇ ::
//                 0 <= (if k₂₉ < 100000 then earlier(k₂₉, V?₁₀) else aa₅[k₂₉]))
//       && 0 <= n₂₈ < n₂₂
//       ==> 0 <= (if n₂₈ < 100000 then earlier(n₂₈, V?₁₀) else aa₅[n₂₈])
