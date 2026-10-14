// ./Cuvee.sh -teq -include teq:aggregation -entry main -prove examples/dafny/algorithms/distinct.dfy
// whether the first n elements of a are distinct, by comparing each element with the later ones in an inner loop
//
// status (Oct 14, 2026): verified with -teq -prove; the wrong postcondition d <==> !distincts(...) leaves a goal;
// the inner loop is a value of the outer update, a flag trace from the outer value d that is cleared when a later
// element equals a[k], which current_flag_nodup names d && nodup(a, k, k + 1 + integer(nn)); the outer trace is then
// the conjunction of nodup over the iterations, with the numbers of inner iterations nn a choice that the two
// constraints of the inner loop fix to n - k - 1; current_distinct_steps takes them as closed side conditions (the
// first binds the bound len, named apart from the method's n, since a rule variable of the same name as a variable of
// the goal makes the condition coincide with the fact literally, without binding it) and names the result

// whether a[k] does not occur among a[k + 1..h)
function nodup(a: array<int, int>, k: int, h: int): bool

// the inner loop: a flag that is cleared when a later element equals a[k], scanned from k + 1 for nn steps
lemma {:rw} current_flag_nodup(a: array<int, int>, d: bool, k: int, nn: Nat)
  ensures current(trace(d, for ⌊counter(0, 1, nn)⌋, ⌊counter(k + 1, 1, nn)⌋ do x, i, j ::
            case a[k] == a[j] => false case a[k] != a[j] => x))
    == (d && nodup(a, k, k + 1 + integer(nn)))

// the outer loop: the conjunction of nodup over the iterations, with the numbers of inner iterations fixed by the two
// constraints of the inner loop to len - k - 1, is the distinctness of a[0..len); len is bound by the first constraint
lemma {:rw} current_distinct_steps(a: array<int, int>, len: int, m: Nat, ns: List<Nat>)
  requires invs(for ⌊counter(0, 1, m)⌋, ns check k, nn :: len <= integer(nn) + k + 1)
  requires invs(for ⌊counter(0, 1, m)⌋, ns check k, nn :: nn == zero || k + 1 < len && integer(nn) + k < len)
  requires len == integer(m)
  ensures current(trace(true, for ⌊counter(0, 1, m)⌋, ns do d, k, nn :: d && nodup(a, k, k + 1 + integer(nn))))
    == distincts(selects(a, ⌊counter(0, 1, natural(len))⌋))

method main(a: array<int, int>, n: int) returns (d: bool)
  requires 0 <= n
  ensures d <==> distincts(selects(a, ⌊counter(0, 1, natural(n))⌋))
{
  var i: int;
  var j: int;
  d := true;
  i := 0;
  while i < n
  {
    j := i + 1;
    while j < n
    {
      if a[i] == a[j] {
        d := false;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
