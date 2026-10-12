// ./Cuvee.sh -vcgen -monomorph -z3 examples/boogie/vcgen/invalid_call_globals.bpl
// expected: invalid
// calls modify the global variables in the modifies clause of the callee

var counter: int;

procedure incr()
  ensures counter > 0;
  modifies counter;
{
  counter := 1;
}

procedure caller()
  ensures counter == 0;
  modifies counter;
{
  counter := 0;
  call incr();
}
