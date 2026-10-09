// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loop-acceleration/phases_1-1.dfy
// SV-COMP loop-acceleration/phases_1-1.yml (expected: safe), translated from the C program by
// hand: x counts by 1 up to 65520 (0xfff0), then by 2 up to 268435455 (0x0fffffff), and is even then
//
// findings: the update has two phases, by 1 below 65520 and by 2 from there on, which the lemma accelerates for a
// generic bound b and step c, as a conditional by the number of iterations; -split splits it into cases, the first
// is contradictory with the exit, and the second is even, since even summands do not change the remainder modulo 2;
// closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here
// note: the concrete loop bounds are symbolic, arbitrary values that keep the verdict: N for 268435455, above the
// threshold 65520

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// a counter in two phases: by 1 up to the bound b, from an initial value up to b, then by c
lemma {:rw} {:teq} current_1(x0: int, n: int, b: int, c: int)
  ensures if x0 <= b
    then current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x < b => x + 1 case b <= x => x + c))
           == if n <= b - x0 then x0 + n else b + (n - (b - x0)) * c

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
