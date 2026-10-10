// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/gnome_sort.dfy
// gnome sort: a single loop whose position moves down at a descent and up otherwise, so that the number of
// iterations is not a counter; expected to stay open, as a negative example of the loop shapes that trace
// equation systems model
//
// status: open, as expected: the position i and the array b are traces over each other with the guard
// b[i - 1] <= b[i], the number of iterations is not related to n (the exit n <= i only bounds it from below), and the
// swaps are at i and i - 1, arithmetic on a bound variable; no shape of teq.dfy or of the examples applies

function sorted(a: array<int, int>, lo: int, hi: int): bool
function perm(a: array<int, int>, b: array<int, int>): bool

method main(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures sorted(b, 0, n)
  ensures perm(b, a)
{
  var i: int;
  var t: int;
  b := a;
  i := 1;
  while i < n
  {
    if i == 0 || b[i - 1] <= b[i] {
      i := i + 1;
    } else {
      t := b[i];
      b[i] := b[i - 1];
      b[i - 1] := t;
      i := i - 1;
    }
  }
}
