// expected: valid
// declarations: sorts, constants, polymorphic functions, axioms, quantifiers;
// statements: havoc, nondeterministic choice, break, return

type Elem;
type List<a>;
type Pair = [int]bool;
type Fun<a, b> = [a]b;

const zero, one: int;
const e: Elem;

axiom {:name "constants"} {:weight 1, 2} zero == 0 && one == 1;

function nil<a>(): List<a>;
function cons<a>(x: a, xs: List<a>): List<a>;
function length<a>(xs: List<a>): int;

axiom (forall x: Elem, xs: List<Elem> :: { length(cons(x, xs)) } length(cons(x, xs)) == length(xs) + 1);
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
