// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-lopstr16/single_elem_safe.dfy
// SV-COMP array-lopstr16/single_elem_safe.yml (expected: safe), translated from the C program by hand:
// pointers are only compared with null, they are modeled by truth values, whether they are not null, where
// malloc does not fail; the fields of structs are arrays of their own; each struct is allocated if q == 0, with
// n = q % 2, and its pointer p is allocated if n == 0; then a[3] is a fresh struct with arbitrary fields; for i
// != 3, allocated structs with n == 0 are checked to have p allocated
//
// findings: the fields are stored under the case split q == 0, joined, or read as guarded stores, by the lemmas of
// base_case and motivex; the read past the store at position 3 needs read over write at a different position, which
// the simplifier decides without the facts of the context (Simplify.select with ctx.neutral), so that the
// hypothesis j != 3 does not help; a lemma for it, whose side condition is decided against the facts, closes it (no
// output) (see TODO.md)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

// a store at the iteration k whose value depends on a case split on the values of the iteration is a store of the
// conditional value (with two further dependencies hs and xs)
lemma {:rw} {:teq} trace_1<b>(a0: array<int, b>, n: Nat, hs: List<int>, xs: List<int>, C: (int, int) -> bool,
                              F: (int, int) -> b, G: (int, int) -> b)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, hs, xs do a, k, h, x :: case C(h, x) => a[k := F(h, x)] case !C(h, x) => a[k := G(h, x)])
      == trace(a0, for ⌊counter(0, 1, n)⌋, hs, xs do a, k, h, x :: a[k := if C(h, x) then F(h, x) else G(h, x)])

// a store at the iteration k that is made only if C holds of the values of the iteration, read at j: the value of
// the iteration j if it is one of the first n and C holds there, otherwise the initial value (with further
// dependencies hs and xs)
lemma {:rw} {:teq} current_1<b>(a0: array<int, b>, n: Nat, j: int, hs: List<int>, xs: List<int>, C: (int, int) -> bool,
                                V: (int, int) -> b)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, hs, xs do a, k, h, x :: case C(h, x) => a[k := V(h, x)] case !C(h, x) => a))[j]
      == if 0 <= j < integer(n) && C(earlier(natural(j), hs), earlier(natural(j), xs)) then V(earlier(natural(j), hs), earlier(natural(j), xs)) else a0[j]

method main() {
  var N: int;
  var i: int;
  var q: int;
  var v: int;
  var w: bool;
  var s: array<int, bool>;
  var n: array<int, int>;
  var p: array<int, bool>;
  assume 0 < N;
  i := 0;
  while i < N {
    q := *;
    if q == 0 {
      s := s[i := true];
      n := n[i := rem(q, 2)];
      if n[i] == 0 {
        p := p[i := true];
      } else {
        p := p[i := false];
      }
    } else {
      s := s[i := false];
    }
    i := i + 1;
  }
  v := *;
  w := *;
  s := s[3 := true];
  n := n[3 := v];
  p := p[3 := w];
  i := 0;
  while i < N {
    if i != 3 && s[i] && n[i] == 0 {
      assert p[i];
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
