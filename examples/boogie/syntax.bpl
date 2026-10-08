// ./Cuvee.sh -verify -monomorph -z3 examples/boogie/syntax.bpl
// expected: valid
// declarations: sorts, constants, polymorphic functions, axioms, quantifiers;
// statements: havoc, nondeterministic choice, break, return

type Elem;
type Stack<a>;
type Pair = [int]bool;
type Fun<a, b> = [a]b;

const {:name "constants"} {:weight 1, 2} zero, one: int;
const e: Elem;

axiom zero == 0 && one == 1;

function nil<a>(): Stack<a>;
function cons<a>(x: a, xs: Stack<a>): Stack<a>;
function length<a>(xs: Stack<a>): int;

axiom (forall x: Elem, xs: Stack<Elem> :: { length(cons(x, xs)) } length(cons(x, xs)) == length(xs) + 1);
axiom (exists n: int :: n div 2 == 1 && n mod 2 == 0);

function {:inline} double(x: int): int { x + x }

procedure {:entry} /* comment */ choose(x: int) returns (y: int)
  ensures y == x || y == -x;
  ensures x == zero ==> y == zero;
{
  havoc y;
  if (*) {
    y := x;
  } else if (x != 0) {
    y := -x;
  } else {
    y := x;
    return;
  }

  while (true) {
    break;
  }
}
