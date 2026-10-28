// ./Cuvee.sh -prove -prove:steps 1 examples/dafny/prove/steps.dfy
// the bound on the rewrite steps of -prove: the goal needs two steps of the rule g_id, one more than the bound, so
// rewriting is reported not to terminate
function g(x: int): int

lemma {:rw} g_id(x: int)
  ensures g(x) == x

lemma twice()
  ensures g(g(3)) == 3
