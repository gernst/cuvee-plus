// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_partition_original_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_partition_original_ground.yml (expected: safe), translated from the C program by hand:
// the nonnegative elements of an arbitrary array are compacted into bb and the negative ones into cc, which are
// checked
//
// findings: error: rewriting does not terminate, with the rule of teq.dfy for earlier(k, ⌊counter(i, c, n)⌋), as
// for standard_partition_ground-2 (counts over prefixes, see TODO.md)

method main() {
  var i: int;
  var a: int;
  var b: int;
  var c: int;
  var x: int;
  var v: int;
  var aa: array<int, int>;
  var bb: array<int, int>;
  var cc: array<int, int>;
  a := 0;
  b := 0;
  c := 0;
  i := 0;
  while i < 100000 {
    havoc v;
    aa := aa[i := v];
    i := i + 1;
  }
  while a < 100000 {
    if aa[a] >= 0 {
      bb := bb[b := aa[a]];
      b := b + 1;
    } else {
      cc := cc[c := aa[a]];
      c := c + 1;
    }
    a := a + 1;
  }
  x := 0;
  while x < b {
    assert bb[x] >= 0;
    x := x + 1;
  }
  x := 0;
  while x < c {
    assert cc[x] < 0;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// error "rewriting does not terminate"
//   "Rule(Set(),Set(Var(Name(k,None),Sort(Con(Name(Int,None),0),List())), Var(Name(i,None),Sort(Con(Name(Int,None),0),List())), Var(Name(c,None),Sort(Co ... (shortened)
