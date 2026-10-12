// ./Cuvee.sh -vcgen -monomorph -z3 examples/boogie/vcgen/invalid_loop_globals.bpl
// expected: invalid
// loops modify the global variables in their modifies clause

var counter: int;

procedure incr()
  ensures counter > 0;
  modifies counter;
{
  counter := 1;
}

procedure loop()
  ensures counter == 0;
  modifies counter;
{
  var i: int;
  i := 0;
  counter := 0;
  while (i < 1)
    invariant true;
    modifies counter;
  {
    call incr();
    i := i + 1;
  }
}
