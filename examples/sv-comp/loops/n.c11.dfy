// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/n.c11.dfy
// SV-COMP ReachSafety-Loops/loops/n.c11.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: len counts up to 4 and is reset to 0 there, while a[len] is set to 0, and 0 <= len < 5 is checked
//
// findings: len is a counter that is reset to 1 when it reaches 4; two lemmas, generic in the reset value d and the
// bound m, bound such a counter from below and, if it is reset to at most m, from above; closed (no output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀

// a counter that is reset to d when it reaches m, and incremented otherwise, stays above a lower bound of its
// initial value and d, and, if it starts at most at m and is reset to at most m, below an upper bound above m; the
// left-hand sides are comparisons
lemma {:rw} {:free} {:teq} forall x0: int, n: int, m: int, d: int, lo: int ::
  if lo <= x0 && lo <= d
  then lo <= current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x == m => d case x != m => x + 1))
lemma {:rw} {:free} {:teq} forall x0: int, n: int, m: int, d: int, hi: int ::
  if x0 <= m && d <= m && m < hi
  then current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x == m => d case x != m => x + 1)) < hi

method main() returns (result: int) {
  var tmp₁: bool;
  {
    var a: array<int, int>, len: int, i: int;
    len := 0;
    while true {
      havoc tmp₁;
      if !tmp₁ {
        break;
      }
      {
        if len == 4 {
          len := 0;
        }
        a := a[len := 0];
        len := len + 1;
      }
    }
    assert len >= 0 && len < 5;
    result := 1;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
