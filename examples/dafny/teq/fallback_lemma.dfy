// ./Cuvee.sh -teq -fallback -z3 examples/dafny/teq/fallback_lemma.dfy
// a lemma over traces that is not free is lowered and checked like a goal: the lowering generalizes the equation of
// whole traces by a fresh function, hence the lemma is unknown, whereas a free lemma is assumed, dropped since it
// cannot be expressed, and has no answer; the goal of the method is correct
lemma same(m: Nat)
  ensures counter(0, 1, m) == counter(0, 1, m)
{
}

lemma assumed(m: Nat)
  ensures counter(0, 1, m) == counter(0, 1, m)

method main(a: int) returns (b: int)
  ensures b == a
{
  b := a;
}
