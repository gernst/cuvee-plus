// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/loopv1.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/loopv1.yml (expected: safe), translated from the C program by hand: i
// increases by 6 or by 3, chosen arbitrarily, up to n, at most SIZE == 50000001, and is a multiple of 3 then
//
// findings: i increases by 6 or 3, chosen arbitrarily; the lemma states that a value whose two increments are
// multiples of m keeps its remainder modulo m, a modular invariant, matched by the remainder i % 3 of the
// assertion; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var n: int;
  var i: int;
  var j: int;
  var c: int;
  havoc n;
  assume n <= 50000001;
  i := 0;
  j := 0;
  while i < n {
    havoc c;
    if c != 0 {
      i := i + 6;
    } else {
      i := i + 3;
    }
  }
  assert i % 3 == 0;
}

// remaining goals of -teq -simplify:
// none
