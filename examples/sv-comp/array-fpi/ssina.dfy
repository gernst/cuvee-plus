// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/ssina.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/ssina.yml (expected: safe), translated from the C program by hand: a is set
// to 1, its sum N added to each element, and the new sum N * (N + 1) added again, which gives (N + 1) * (N + 1)
//
// findings: the sum over the array after stores of constants at the counter is read at another counter with the
// same definition, which the lemma of teq.dfy for reads of stores at the same keys does not match, since the keys
// are compared literally; a lemma for counters of the same length, matched through the definitions, closes it (no
// output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function stores<a, b>(a: array<a, b>, keys: seq<a>, values: seq<b>): Trace<array<a, b>>
function selects<a, b>(a: array<a, b>, keys: seq<a>): seq<b>

// the reads of stores at the positions of a counter, at the positions of a counter of the same length, are the stored
// values; teq.dfy states this for the same keys, which are compared literally, here ⌊K⌋ and ⌊I⌋ of two counters
// with the same definition
lemma {:rw} {:free} {:teq} forall a: array<int, int>, n: int, vs: seq<int> ::
  selects(current(stores(a, ⌊counter(0, 1, n)⌋, vs)), ⌊counter(0, 1, n)⌋) == vs

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
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
    sum := sum + a[i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] + sum];
    i := i + 1;
  }
  sum := 0;
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] + sum];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == (N + 1) * (N + 1);
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
