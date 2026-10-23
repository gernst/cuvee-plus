// ./Cuvee.sh -implement examples/dafny/transform/invalid_implement_body.dfy
// the body of an implementation is not rewritten: the implemented function f applied there would stay uninterpreted
// on representations, hence an error
function f(x: int): int
function g(x: int): int

function {:implement f(x)} f1(x: int): int { x + 1 }
function {:implement g(x)} g1(x: int): int { f(x) }

method m(x: int) returns (y: int)
{
  y := g(x);
}
