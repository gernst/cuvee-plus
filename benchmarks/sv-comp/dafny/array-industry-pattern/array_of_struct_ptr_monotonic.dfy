// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-industry-pattern/array_of_struct_ptr_monotonic.dfy
// SV-COMP array-industry-pattern/array_of_struct_ptr_monotonic.yml (expected: safe), translated from the C program by hand:
// pointers are only compared with null, they are modeled by truth values, whether they are not null, where
// malloc does not fail; at the even positions, each struct gets a value t and a pointer p1 that is allocated if
// t == 10, and is uninitialized (arbitrary) otherwise, which is checked at the even positions
//
// findings: the loops step by 2, which -teq expresses by the counter ⌊counter(0, 2, n)⌋ as a dependency, at which
// the guarded stores are made; lemmas join the guarded stores at a position given by a dependency, and resolve
// occurs and indexof of an even position in the counter with step 2, stated for the literal 2, since a variable
// does not match a literal coefficient; the remaining 2 * n / 2 needs cancellation, and the equation of a
// conditional a case split, both lemmas not about traces; closed (no output) (array_of_struct_ptr_cond_init,
// array_of_struct_ptr_flag_init, array_ptr_partial_init, array_of_struct_break, and array_of_struct_ptr_mul_init
// are variants of array-lopstr16 tasks and are not translated)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// a store at a position given by a dependency ps, e.g. a counter with step 2, whose value depends on a case split on
// the values of the iteration, is a store of the conditional value (with one or two further dependencies)
lemma {:rw} {:teq} trace_1<b>(a0: array<int, b>, n: Nat, ps: List<int>, xs: List<int>, C: (int) -> bool, F: (int) -> b,
                              G: (int) -> b)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, ps, xs do a, k, p, x :: case C(x) => a[p := F(x)] case !C(x) => a[p := G(x)])
      == trace(a0, for ⌊counter(0, 1, n)⌋, ps, xs do a, k, p, x :: a[p := if C(x) then F(x) else G(x)])
lemma {:rw} {:teq} trace_2<b>(a0: array<int, b>, n: Nat, ps: List<int>, xs: List<int>, ys: List<b>, C: (int) -> bool,
                              F: (int, b) -> b, G: (int, b) -> b)
  ensures trace(a0, for ⌊counter(0, 1, n)⌋, ps, xs, ys do a, k, p, x, y ::
          case C(x) => a[p := F(x, y)] case !C(x) => a[p := G(x, y)])
    == trace(a0, for ⌊counter(0, 1, n)⌋, ps, xs, ys do a, k, p, x, y :: a[p := if C(x) then F(x, y) else G(x, y)])

lemma {:rw} {:teq} lemma_2<b>(c: bool, x: b, y: b, z: b)
  ensures (if c then x else y) == z <==> if c then x == z else y == z

method main() {
  var N: int;
  var i: int;
  var x: int;
  var y: bool;
  var t: array<int, int>;
  var p1: array<int, bool>;
  assume 0 < N;
  i := 0;
  while i < N {
    x := *;
    t := t[i := x];
    if x == 10 {
      p1 := p1[i := true];
    } else {
      y := *;
      p1 := p1[i := y];
    }
    i := i + 2;
  }
  i := 0;
  while i < N {
    if t[i] == 10 {
      assert p1[i];
    }
    i := i + 2;
  }
}

// remaining goals of -teq -simplify:
// none
