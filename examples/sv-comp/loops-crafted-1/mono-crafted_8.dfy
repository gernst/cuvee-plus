// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/mono-crafted_8.dfy
// SV-COMP ReachSafety-Loops/loops-crafted-1/mono-crafted_8.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: z counts down from 5000000 in the second half of x up to 10000000, and z == 0 is checked
//
// findings: z counts down only in the iterations from 5000000 on; a lemma states the closed form of such a
// two-phase counter, generic in the start c and the step d; closed (no output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// a value that changes by d from the iteration c >= 0 on, and is kept before, a two-phase counter (with a further
// dependency ys)
lemma {:rw} {:free} {:teq} forall x0: int, n: int, c: int, d: int, ys: seq<int> ::
  if 0 <= c
  then current(trace(x0, for ⌊counter(0, 1, n)⌋, ys do z, k, y :: case c <= k => z + d case k < c => z))
    == if n <= c then x0 else x0 + (n - c) * d

method main() returns (result: int) {
  {
    var x: int, y: int, z: int;
    x := 0;
    y := 10000000;
    z := 5000000;
    while x < y {
      if x >= 5000000 {
        z := z - 1;
      }
      x := x + 1;
    }
    assert z == 0;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
