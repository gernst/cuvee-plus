// ./Cuvee.sh -teq -simplify examples/sv-comp/array-lopstr16/base_case.dfy
// SV-COMP ReachSafety-Arrays/array-lopstr16/base_case.yml (expected: safe), translated from the C program by hand:
// pointers are only compared with null, they are modeled by truth values, whether they are not null, where
// malloc does not fail; the fields of structs are arrays of their own; each struct gets a value n and a pointer
// p that is allocated if n == 0, which is checked
//
// findings: the two fields are stored under the same case split on the value x of the iteration; a lemma joins the
// guarded stores into a store of a conditional value, polymorphic in the element type, after which teq.dfy reads
// the stores; closed (no output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>

// a store at the iteration k whose value depends on a case split on the values of the iteration is a store of the
// conditional value (with two further dependencies hs and xs)
lemma <b> {:rw} {:free} {:teq} forall a0: array<int, b>, n: int, hs: seq<int>, xs: seq<int>,
                               C: (int, int) -> bool, F: (int, int) -> b, G: (int, int) -> b ::
  trace(a0, for ⌊counter(0, 1, n)⌋, hs, xs do a, k, h, x :: case C(h, x) => a[k := F(h, x)] case !C(h, x) => a[k := G(h, x)])
    == trace(a0, for ⌊counter(0, 1, n)⌋, hs, xs do a, k, h, x :: a[k := if C(h, x) then F(h, x) else G(h, x)])

method main() {
  var i: int;
  var x: int;
  var n: array<int, int>;
  var p: array<int, bool>;
  i := 0;
  while i < 1000000 {
    havoc x;
    n := n[i := x];
    if x == 0 {
      p := p[i := true];
    } else {
      p := p[i := false];
    }
    i := i + 1;
  }
  i := 0;
  while i < 1000000 {
    if n[i] == 0 {
      assert p[i];
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
