// ./Cuvee.sh -verify -monomorph -z3 examples/boogie/globals.bpl
// expected: valid
// global variables, which procedures and loops declare as modified

var counter: int;
var limit: int;

procedure incr()
  requires counter < limit;
  ensures counter <= limit;
  modifies counter;
{
  counter := counter + 1;
}

procedure fill()
  requires 0 <= counter && counter <= limit;
  ensures counter == limit;
  modifies counter;
{
  while (counter < limit)
    invariant counter <= limit;
    modifies counter;
  {
    call incr();
  }
}
