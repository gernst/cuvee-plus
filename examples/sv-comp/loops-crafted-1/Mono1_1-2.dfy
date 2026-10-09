// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loops-crafted-1/Mono1_1-2.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/Mono1_1-2.yml (expected: safe), translated from the C program by hand:
// x counts by 1 up to 10000000 and by 2 up to 100000000, which it hits exactly
//
// findings: a counter in two phases, by 1 and then by 2, which the lemma of phases_1-1 accelerates; the exact exit
// value needs the last value before the exit, which a second lemma gives: the counter is increasing, hence the
// iteration constraint, an upper bound of its values, holds iff it holds at the last of them; -split splits the
// phases, and the case of the second phase is decided by integers, 100000000 < 2 * n - 10000000 < 100000002 has no
// solution; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// a counter in two phases: by 1 up to the bound b, from an initial value up to b, then by c (see phases_1-1)
lemma {:rw} {:free} {:teq} forall x0: int, n: int, b: int, c: int ::
  if x0 <= b
  then current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x < b => x + 1 case b <= x => x + c))
         == if n <= b - x0 then x0 + n else b + (n - (b - x0)) * c

method main() {
  var x: int;
  x := 0;
  while x < 100000000 {
    if x < 10000000 {
      x := x + 1;
    } else {
      x := x + 2;
    }
  }
  assert x == 100000000;
}

// remaining goals of -teq -simplify -split -simplify:
// none
