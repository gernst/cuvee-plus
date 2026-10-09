// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_partition_ground-2.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_partition_ground-2.yml (expected: safe), translated from the C
// program by hand: the nonnegative elements of aa are collected in bb, counted by b, the negative ones in cc,
// counted by c, and the collected elements of bb are nonnegative
//
// findings: rewriting does not terminate with the lemmas of teq.dfy alone, as in standard_partial_init_ground: the
// positions of bb are given by the counter b of the guarded iterations, whose reads earlier(k, ⌊B⌋) become counts
// over prefixes, which build the contexts of the iterations again; a lemma on the values stored at such positions
// (all satisfy the guard) cannot apply before, no lemma is added
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var aa: array<int, int>;
  var bb: array<int, int>;
  var cc: array<int, int>;
  var a: int;
  var b: int;
  var c: int;
  var i: int;
  var x: int;
  var tmp: int;
  assume 0 < N;
  a := 0;
  b := 0;
  c := 0;
  i := 0;
  while i < N {
    tmp := *;
    aa := aa[i := tmp];
    i := i + 1;
  }
  while a < N {
    if aa[a] >= 0 {
      bb := bb[b := aa[a]];
      b := b + 1;
    }
    a := a + 1;
  }
  a := 0;
  while a < N {
    if aa[a] < 0 {
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
}

// remaining goals of -teq -simplify:
// error "rewriting does not terminate"
//   "Rule(Set(),Set(Var(Name(k,None),Sort(Con(Name(Int,None),0),List())), Var(Name(i,None),Sort(Con(Name(Int,None),0),List())), Var(Name(c,None),Sort(Co ... (shortened)
