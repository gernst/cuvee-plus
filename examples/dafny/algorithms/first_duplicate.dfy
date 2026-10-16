// ./Cuvee.sh -teq -entry main -prove -split -prove examples/dafny/algorithms/first_duplicate.dfy
// whether a[0..n) has a duplicate, with an early exit of both loops by a flag that stops them (distinct.dfy runs
// all iterations); a search in a nested loop
//
// status (Oct 16, 2026): verified with -teq -prove -split -prove; with the conclusion of either implication negated,
// a goal remains (r ==> distincts(...)) or the run does not finish within 180 s (!r ==> !distincts(...)); the inner
// loop is a value of the outer update, folded into scan(x, a, i, nn) over the numbers of inner iterations N? (a
// choice); -split separates the cases of the postcondition, and the two rules on the atom distincts(...) take the
// final flag as it stands among the facts: set, some scan found a[i] == a[j] with j < n by the constraint of the inner
// loop; reset, the flag was reset at the head of every outer iteration, hence every scan ran up to n by its exit
// without a match; the outer counter is an open variable Kv identified with K by its equation, since the instance
// of a side condition over two equal dependencies ⌊counter(0, 1, m)⌋ normalizes to one and is not found among the
// facts, which keep ⌊K⌋ and ⌊counter(0, 1, m)⌋ apart; the outer loop ran up to i >= n is stated with m == natural(i),
// as -split relates the number of iterations and i only by it

// the inner loop in iteration i of the outer loop: the flag x is set once a[i] equals a later a[j]
function {:fold} scan(x: bool, a: array<int, int>, i: int, nn: Nat): Trace<bool>
{
  trace(x, for ⌊counter(0, 1, nn)⌋, ⌊counter(i + 1, 1, nn)⌋ do r, kk, j :: case a[i] == a[j] => true case a[i] != a[j] => r)
}

// the flag is set at the end: some scan found a[i] == a[j], where j < n by the constraint of the inner loop (it ran
// only while j < n), and i < j, hence the elements are not distinct
lemma {:rw} distincts_flag_set(a: array<int, int>, n: int, m: Nat, ns: List<Nat>, Kv: Trace<int>)
  requires Kv == counter(0, 1, m)
  requires current(trace(false, for ⌊Kv⌋, ns, ⌊counter(0, 1, m)⌋ do x, k, nn, i :: current(scan(x, a, i, nn))))
  requires invs(for ⌊Kv⌋, ⌊counter(0, 1, m)⌋, ns check k, i, nn :: nn == zero || i + 1 < n && integer(nn) + i < n)
  ensures distincts(selects(a, ⌊counter(0, 1, natural(n))⌋)) <==> false

// the flag is reset at the end and the outer loop ran up to i >= n (m == natural(i)): the flag was reset at the head of
// every iteration, hence every scan started reset and ended reset, at the end only, i.e. it ran up to n, by its exit,
// without a match; hence no element has a later duplicate (for i < 0, n <= i < 0 and the range is empty)
lemma {:rw} distincts_flags_reset(a: array<int, int>, n: int, m: Nat, ns: List<Nat>, i0: int, Kv: Trace<int>)
  requires Kv == counter(0, 1, m)
  requires !current(trace(false, for ⌊Kv⌋, ns, ⌊counter(0, 1, m)⌋ do x, k, nn, i :: current(scan(x, a, i, nn))))
  requires invs(for ⌊Kv⌋,
                    ⌊trace(false, for ⌊Kv⌋, ns, ⌊counter(0, 1, m)⌋ do x, k, nn, i :: current(scan(x, a, i, nn)))⌋,
                    ⌊counter(0, 1, m)⌋
                check k, x, i :: !x)
  requires invs(for ⌊Kv⌋, ⌊counter(0, 1, m)⌋, ns
                check k, i, nn :: !(integer(nn) + i + 1 < n && !current(scan(false, a, i, nn))))
  requires m == natural(i0) && n <= i0
  ensures distincts(selects(a, ⌊counter(0, 1, natural(n))⌋)) <==> true

method main(a: array<int, int>, n: int) returns (r: bool)
  requires 0 <= n
  // the postcondition as two implications: the exit !(i < n && !r) of the outer loop is then a literal in the context
  // of each (as the equivalence, the goal's conclusion is i < n && !r || r == !distincts(...), where the rule on
  // distincts(...) sees neither n <= i nor r, NOTES.md)
  ensures r ==> !distincts(selects(a, ⌊counter(0, 1, natural(n))⌋))
  ensures !r ==> distincts(selects(a, ⌊counter(0, 1, natural(n))⌋))
{
  var i: int;
  var j: int;
  r := false;
  i := 0;
  while i < n && !r
  {
    j := i + 1;
    while j < n && !r
    {
      if a[i] == a[j] {
        r := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
