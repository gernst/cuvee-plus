// ./Cuvee.sh -teq -simplify examples/sv-comp/array-industry-pattern/array_of_struct_single_elem_init.dfy
// SV-COMP array-industry-pattern/array_of_struct_single_elem_init.yml (expected: safe), translated from the C program by hand:
// each struct gets a value n and p = 10 if n == 0, else 20; then a[3] gets n = 40 and p = 30; for i != 3, n ==
// 0 implies p == 10, which is checked (the fields are arrays of their own)
//
// findings: as array-lopstr16/single_elem_safe, by the lemmas joining guarded stores and for reads over writes at a
// different position, and a lemma that an equation of a conditional is a case split; closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// a store at the iteration k whose value depends on a case split on the values of the iteration is a store of the
// conditional value (with two further dependencies hs and xs)
lemma {:rw} {:teq} trace_1<b>(a0: array<int, b>, n: Nat, hs: List<int>, xs: List<int>, C: (int, int) -> bool,
                              F: (int, int) -> b, G: (int, int) -> b)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, hs, xs do a, k, h, x :: case C(h, x) => a[k := F(h, x)] case !C(h, x) => a[k := G(h, x)])
      == trace(a0, for ⌊counter(0, 1, n)⌋, hs, xs do a, k, h, x :: a[k := if C(h, x) then F(h, x) else G(h, x)])

// read over write at a different position, whose side condition is decided against the facts of the context, which
// the simplifier does not consult for reads over writes (see TODO.md)
lemma {:rw} {:teq} lemma_1<b>(a: array<int, b>, i: int, j: int, v: b)
  requires j != i
  ensures a[i := v][j] == a[j]

// an equation of a conditional is a case split (not about traces)
lemma {:rw} {:teq} lemma_2<b>(c: bool, x: b, y: b, z: b)
  ensures (if c then x else y) == z <==> if c then x == z else y == z

method main() {
  var N: int;
  var i: int;
  var q: int;
  var x: int;
  var n: array<int, int>;
  var p: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    q := *;
    x := *;
    if x == 0 {
      p := p[i := 10];
    } else {
      p := p[i := 20];
    }
    n := n[i := x];
    i := i + 1;
  }
  p := p[3 := 30];
  n := n[3 := 40];
  i := 0;
  while i < N {
    if i != 3 && n[i] == 0 {
      assert p[i] == 10;
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
