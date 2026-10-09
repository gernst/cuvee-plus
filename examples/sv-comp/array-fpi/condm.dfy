// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-fpi/condm.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/condm.yml (expected: safe), translated from the C program by hand: a of
// arbitrary size N is set to 0, then 2 or 1 is added to each element, depending on the parity of N, which the
// elements have then
//
// findings: the guard N % 2 == 0 of the update is the same in all iterations; the two cases store at the same
// position, which a lemma joins into one store of a conditional value (see standard_running-2), which teq.dfy
// accelerates, and -split splits the remaining conditional, with the remainder lemma; closed (no output). Attempt:
// the lemma that splits such a trace into two (see diamond_1-1) does not terminate, since it also matches the
// resulting single-case traces, where one case of the pattern covers the update, with c := true and the function of
// the other case uninstantiated (see TODO.md); the joined store is accelerated before

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀

// two cases that store at the same position, the iteration, are one store of a conditional value (see
// standard_running-2), here with values that read the array itself
lemma {:rw} {:free} {:teq} forall a0: array<int, int>, n: int, hs: seq<int>, C: (int, int) -> bool,
                           F: (array<int, int>, int, int) -> int, G: (array<int, int>, int, int) -> int ::
  trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: case C(k, h) => a[k := F(a, k, h)] case !C(k, h) => a[k := G(a, k, h)])
    == trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: a[k := if C(k, h) then F(a, k, h) else G(a, k, h)])

// the remainder modulo 2 is 0 or 1 (arithmetic, not about traces)
lemma {:rw} {:free} {:teq} forall y: int ::
  !(y % 2 == 0) <==> y % 2 == 1

method main() {
  var N: int;
  var a: array<int, int>;
  var i: int;
  N := *;
  assume 0 < N <= 536870911;
  i := 0;
  while i < N {
    a := a[i := 0];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if N % 2 == 0 {
      a := a[i := a[i] + 2];
    } else {
      a := a[i := a[i] + 1];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] % 2 == N % 2;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
