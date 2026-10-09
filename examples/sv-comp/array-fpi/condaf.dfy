// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/condaf.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/condaf.yml (expected: unsafe), translated from the C program by hand: the
// unsafe variant of conda, which increases the elements that are 0, of which there are none, and decreases the
// others
//
// findings: unsafe, not closed with the lemmas of conda, as expected
// note: 1 of its lemmas are part of teq.dfy now and are removed here

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function sum(values: seq<int>): int

// two cases that store at the same position, the iteration, are one store of a conditional value (see condm)
lemma {:rw} {:free} {:teq} forall a0: array<int, int>, n: int, hs: seq<int>, C: (array<int, int>, int, int) -> bool,
                           F: (array<int, int>, int, int) -> int, G: (array<int, int>, int, int) -> int ::
  trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: case C(a, k, h) => a[k := F(a, k, h)] case !C(a, k, h) => a[k := G(a, k, h)])
    == trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: a[k := if C(a, k, h) then F(a, k, h) else G(a, k, h)])

function stores<a, b>(a: array<a, b>, keys: seq<a>, values: seq<b>): Trace<array<a, b>>
function selects<a, b>(a: array<a, b>, keys: seq<a>): seq<b>

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var sum: int;
  havoc N;
  assume 0 < N <= 536870911;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] == 0 {
      a := a[i := a[i] + 1];
    } else {
      a := a[i := a[i] - 1];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  assert sum == 2 * N;
}

// remaining goals of -teq -simplify:
// goal forall N₅: int :: !(0 < N₅ <= 536870911)
