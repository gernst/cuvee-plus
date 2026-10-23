// ./Cuvee.sh -vcgen -prove examples/dafny/prove/reentrant.dfy
// a rule whose side condition mentions the rule's own left-hand side term: the instance f(a) <= 1 of the condition is
// simplified before it is decided, which rewrote f(a) by the rule itself, whose condition was decided again, without
// end; the rule is suspended while its conditions are evaluated (Context.active), so the condition is decided from
// the hypothesis and the goal closes
function f(x: int): int
function g(x: int): int

lemma {:rw} f_small(x: int)
  requires f(x) <= 1
  ensures f(x) == g(x)

method main(a: int)
  requires f(a) <= 1
  ensures f(a) == g(a)
{
}
