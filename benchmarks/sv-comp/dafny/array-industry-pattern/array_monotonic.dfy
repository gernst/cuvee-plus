// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/dafny/array-industry-pattern/array_monotonic.dfy
// SV-COMP array-industry-pattern/array_monotonic.yml (expected: safe), translated from the C
// program by hand: at the even positions, a is arbitrary and b is 20 where a is 10, which is checked at the even
// positions again
//
// findings: both arrays are written at the even positions, a counter with step 2 that is a dependency of the loop:
// a by two cases with the same position, which a lemma joins into one store of a conditional value, b by stores
// guarded by the arbitrary value, which a lemma reads by occurs and indexof of the positions, given that they are
// distinct, which teq.dfy decides for counters; the positions are kept as the matched dependency, since the facts
// refer to it; a third lemma decides occurs for counters with a positive step, which teq.dfy has for the step 1
// only, with the remainder lemma for the even positions; -split splits the conditionals; closed (no output)
// note: 3 of its lemmas are part of teq.dfy now and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// two cases that store at the same position, here that of a further dependency, are one store of a conditional value
// (see standard_running-2)
lemma {:rw} {:teq} trace_1(a0: array<int, int>, n: Nat, ps: List<int>, cs: List<int>, C: (int, int) -> bool,
                           F: (int, int) -> int, G: (int, int) -> int)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, ps, cs do a, k, p, c :: case C(p, c) => a[p := F(p, c)] case !C(p, c) => a[p := G(p, c)])
      == trace(a0, for ⌊counter(0, 1, n)⌋, ps, cs do a, k, p, c :: a[p := if C(p, c) then F(p, c) else G(p, c)])

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var tmp: int;
  assume 0 < N;
  i := 0;
  while i < N {
    tmp := *;
    a := a[i := tmp];
    if a[i] == 10 {
      b := b[i := 20];
    }
    i := i + 2;
  }
  i := 0;
  while i < N {
    if a[i] == 10 {
      assert b[i] == 20;
    }
    i := i + 2;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
