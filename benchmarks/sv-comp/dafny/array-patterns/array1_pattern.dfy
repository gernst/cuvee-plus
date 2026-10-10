// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-patterns/array1_pattern.dfy
// SV-COMP array-patterns/array1_pattern.yml (expected: safe), translated from the C program by
// hand: two arrays of zeros get index * num * num at index and num * index at N - 1 - index for nondeterministic
// indices until a nondeterministic exit, with num = -1, and the sum of both arrays is checked to be 0
//
// findings: the representative of the folder, whose 37 tasks (30 safe, 7 buggy) store at nondeterministic indices
// until a nondeterministic exit, also in matrices, and check a sum over the whole array; teq.dfy summarizes the
// stores at arbitrary keys as stores(a, Index?, values) and the final sums as sum(selects(..., ⌊counter(0, 1,
// N)⌋)); open: a lemma would need the sum of an array after stores at arbitrary keys within its bounds as the sum
// over the distinct keys of their last values plus the untouched initial values, and here the reindexing of the
// mirrored positions N - 1 - index of the second array; no lemmas tried

method main() {
  var N: int;
  var count: int;
  var num: int;
  var temp: int;
  var index: int;
  var sum: int;
  var array1: array<int, int>;
  var array2: array<int, int>;
  N := *;
  assume N > 0;
  num := -1;
  sum := 0;
  count := 0;
  while count < N {
    array1 := array1[count := 0];
    array2 := array2[count := 0];
    count := count + 1;
  }
  while true {
    index := *;
    assume index >= 0 && index < N;
    array1 := array1[index := num * (num * index)];
    array2 := array2[N - 1 - index := num * index];
    temp := *;
    if temp == 0 {
      break;
    }
  }
  count := 0;
  while count < N {
    sum := sum + array1[count] + array2[count];
    count := count + 1;
  }
  assert sum == 0;
}

// remaining goals of -teq -simplify:
// goal
//   forall array1₇: array<int, int>, array2₈: array<int, int>, N₉: int,
//          array1₁₉: array<int, int>, array2₂₀: array<int, int>,
//          Array1₁₆: Trace<array<int, int>>, Array2₁₇: Trace<array<int, int>>,
//          Count₁₈: Trace<int>, array1₃₈: array<int, int>,
//          array2₃₉: array<int, int>, n₃₀: int, K₃₂: Trace<int>,
//          Array1₃₄: Trace<array<int, int>>, Array2₃₅: Trace<array<int, int>>,
//          Index?₂₈: seq<int>, Temp?₂₉: seq<int>, index₄₁: int, K₅₆: Trace<int> ::
//     array1₁₉ == current(Array1₁₆)
//       && array2₂₀ == current(Array2₁₇)
//       && Array1₁₆ == stores(array1₇, ⌊Count₁₈⌋, ⌊consts(N₉, 0)⌋)
//       && Array2₁₇ == stores(array2₈, ⌊Count₁₈⌋, ⌊consts(N₉, 0)⌋)
//       && Count₁₈ == counter(0, 1, N₉)
//       && K₃₂ == counter(0, 1, n₃₀)
//       && array1₃₈ == current(Array1₃₄)
//       && array2₃₉ == current(Array2₃₅)
//       && Array1₃₄ == stores(array1₁₉, Index?₂₈, Index?₂₈)
//       && Array2₃₅
//         == stores(array2₂₀, maps(for ⌊K₃₂⌋, Index?₂₈
//                                  yield k₃₁, index₂₆ ::
//                                    N₉ + -index₂₆ + -1), maps(for ⌊K₃₂⌋, Index?₂₈
//                                                              yield k₃₁, index₂₆ ::
//                                                                -index₂₆))
//       && invs(for ⌊K₃₂⌋, Index?₂₈ check k₃₁, index₂₆ :: 0 <= index₂₆)
//       && invs(for ⌊K₃₂⌋, Index?₂₈ check k₃₁, index₂₆ :: index₂₆ < N₉)
//       && invs(for ⌊K₃₂⌋, Temp?₂₉ check k₃₁, temp₂₇ :: temp₂₇ != 0)
//       && 0 <= n₃₀
//       && 0 <= index₄₁ < N₉
//       && K₅₆ == counter(0, 1, N₉)
//       ==> sum(selects(array1₃₈, ⌊K₅₆⌋)) + sum(selects(array2₃₉, ⌊K₅₆⌋))
//         == (if occurs(N₉ + -index₄₁ + -1, maps(for ⌊K₃₂⌋, Index?₂₈
//                                                yield k₃₁, index₂₆ ::
//                                                  N₉ + -index₂₆ + -1))
//             then -earlier(indexof(N₉ + -index₄₁ + -1, maps(for ⌊K₃₂⌋, Index?₂₈
//                                                            yield k₃₁, index₂₆ ::
//                                                              N₉
//                                                                + -index₂₆
//                                                                + -1)), Index?₂₈)
//             else 0)
//           + (if occurs(index₄₁, Index?₂₈) then index₄₁ else 0)
