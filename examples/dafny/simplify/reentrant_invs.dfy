// ./Cuvee.sh -teq -prove examples/dafny/simplify/reentrant_invs.dfy
// a rule with a general left-hand side and an iteration constraint as its side condition, the former sum_invs_const
// of the lemma database: the condition is matched against the invs facts of the goal, which builds the context of
// each fact's combinator and normalizes the reads of its dependencies, where earlier_sums turns the read of the trace
// of s into a sum, which the left-hand side matches again, with the same fact, one level deeper; the rule is
// suspended while its conditions are evaluated, and the reads of a context are normalized by the rules without an
// invs condition only, so the run terminates (the goal is closed by the lemmas of the database, not by this rule)
lemma {:rw} sum_invs_const(n: Nat, c: int, js: List<int>)
  requires invs(for ⌊counter(0, 1, n)⌋, js check k, j :: j == c)
  ensures sum(js) == c * integer(n)

method main(n: int, c: int) returns (s: int)
  requires 0 <= n
  ensures s == c * n
{
  var i: int;
  i := 0;
  s := 0;
  while i < n
  {
    s := s + c;
    i := i + 1;
  }
}
