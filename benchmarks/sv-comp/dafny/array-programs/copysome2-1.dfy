// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-programs/copysome2-1.dfy
// SV-COMP array-programs/copysome2-1.yml (expected: safe), translated from the C program by hand:
// a2 is a copy of a1 except at z, and a3 a copy of a2 except at z, where it gets a1[z]; a3 is checked to agree
// with a1
//
// findings: with the lemmas of copysome1-1 (a counter whose two cases agree, and the read of guarded stores at a
// counter), a lemma for the stores of the third loop, whose second case stores at the literal position c that the
// simplifier substituted for i, and a lemma that an equation of a conditional is a case split; closed (no output)
// note: 2 of its lemmas are part of teq.dfy now and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

// lemmas are those of copysome1-1)

// stores at the positions of a counter, of V(i) except at the position c, where the store of d is written at the
// literal c, after the simplifier substituted c for i in that case
lemma {:rw} {:teq} current_1(a0: array<int, int>, n: Nat, j: int, c: int, d: int, V: (int) -> int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case i != c => a[i := V(i)] case i == c => a[c := d]))[j]
      == if 0 <= j < integer(n) then (if j == c then d else V(j)) else a0[j]

// an equation of a conditional is a case split (not about traces)
lemma {:rw} {:teq} lemma_1<b>(c: bool, x: b, y: b, z: b)
  ensures (if c then x else y) == z <==> if c then x == z else y == z

method main() {
  var N: int;
  var i: int;
  var x: int;
  var z: int;
  var v: int;
  var a1: array<int, int>;
  var a2: array<int, int>;
  var a3: array<int, int>;
  assume 0 < N;
  z := 150000;
  i := 0;
  while i < N {
    v := *;
    a1 := a1[i := v];
    v := *;
    a2 := a2[i := v];
    v := *;
    a3 := a3[i := v];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i != z {
      a2 := a2[i := a1[i]];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i != z {
      a3 := a3[i := a2[i]];
    } else {
      a3 := a3[i := a1[i]];
    }
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert a1[x] == a3[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
