// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_find_ground-1.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_find_ground-1.yml (expected: safe), translated from the C
// program by hand: a is filled with arbitrary values, the first index i of e is searched, and no element before i
// is e
//
// findings: the iteration constraint of the search, the elements before the exit differ from e, is abstracted as
// !occurs(e, prefix(n, xs)) with the functions of teq.dfy, which a second lemma instantiates at the positions j < n
// by the atom earlier(j, xs) == e; the assertion fails at some x below the exit only if e occurs there, which
// contradicts it; closed (no output). Attempt: a lemma whose side condition is the iteration constraint and whose
// left-hand side is the comparison j < n does not terminate, since the comparison matches the bounds of the
// iterations in the contexts that matching the iteration constraint builds
// note: 2 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var a: array<int, int>;
  var e: int;
  var i: int;
  var j: int;
  var x: int;
  var tmp: int;
  havoc e;
  i := 0;
  j := 0;
  while j < 100000 {
    havoc tmp;
    a := a[j := tmp];
    j := j + 1;
  }
  while i < 100000 && a[i] != e {
    i := i + 1;
  }
  x := 0;
  while x < i {
    assert a[x] != e;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
