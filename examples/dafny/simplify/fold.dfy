// ./Cuvee.sh -prove examples/dafny/simplify/fold.dfy
// a definition with {:fold} is a rule that folds its body into a call of the function, the converse of {:rw},
// e.g. the functions of teq.dfy that are traces; its formal parameters must occur in the body
function g(x: int): int

function {:fold} twice(x: int): int
{
  g(g(x))
}

goal forall y: int :: g(g(y)) == twice(y)

goal forall y: int :: g(g(y + 1)) > 0
