// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/sanfoundry_02_ground.dfy
// SV-COMP array-examples/sanfoundry_02_ground.yml (expected: safe), translated from the C program by hand:
// the largest and second largest elements of an arbitrary array are computed, and each element is checked to be
// at most the largest, and at most the second largest unless it is the largest
//
// findings: error: rewriting does not terminate, with the rule of teq.dfy for earlier(k, ⌊counter(i, c, n)⌋), on
// the trace of the two largest elements, whose updates read the array at the counter from 2 (see TODO.md)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var x: int;
  var v: int;
  var largest1: int;
  var largest2: int;
  var temp: int;
  var array: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    v := *;
    array := array[i := v];
    i := i + 1;
  }
  largest1 := array[0];
  largest2 := array[1];
  if largest1 < largest2 {
    temp := largest1;
    largest1 := largest2;
    largest2 := temp;
  }
  i := 2;
  while i < N {
    if array[i] >= largest1 {
      largest2 := largest1;
      largest1 := array[i];
    } else if array[i] > largest2 {
      largest2 := array[i];
    }
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert array[x] <= largest1;
    x := x + 1;
  }
  x := 0;
  while x < N {
    assert array[x] <= largest2 || array[x] == largest1;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// error "rewriting does not terminate"
//   "Rule(Set(),Set(Var(Name(k,None),Sort(Con(Name(Int,None),0),List())), Var(Name(i,None),Sort(Con(Name(Int,None),0),List())), Var(Name(c,None),Sort(Co ... (shortened)
