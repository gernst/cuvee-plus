// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loop-acceleration/phases_1-1.dfy
// SV-COMP loop-acceleration/phases_1-1.yml (expected: safe), translated from the C program by hand: x counts by 1
// up to 65520 (0xfff0), then by 2 up to 268435455 (0x0fffffff), and is even then
//
// findings: the update has two phases, by 1 below 65520 and by 2 from there on, which current_trace_two_phases of
// teq.dfy accelerates for a generic bound b and step c >= 0, as a conditional by the number of iterations; -split
// splits it into cases, the first is contradictory with the exit, and the second is even, since even summands do
// not change the remainder modulo 2; closed (no output)
// note: its lemmas are part of teq.dfy now (current_trace_two_phases, mod_add_even) and are removed here
// note: the concrete loop bounds are symbolic, arbitrary values that keep the verdict: N for 268435455, above the
// threshold 65520

method main() {
  var N: int;
  var x: int;
  assume 65520 < N;
  x := 0;
  while x < N {
    if x < 65520 {
      x := x + 1;
    } else {
      x := x + 2;
    }
  }
  assert x % 2 == 0;
}

// remaining goals of -teq -simplify -split -simplify:
// none
