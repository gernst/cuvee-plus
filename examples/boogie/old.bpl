// ./Cuvee.sh -verify -monomorph -z3 examples/boogie/old.bpl
// expected: valid
// old(e) refers to the values of the global variables at the entry of the procedure

var counter: int;

procedure incr(n: int)
  requires 0 <= n;
  ensures counter == old(counter) + n;
  modifies counter;
{
  counter := counter + n;
}

procedure twice(n: int)
  requires 0 <= n;
  ensures old(counter) <= counter && counter == old(counter + 2 * n);
  modifies counter;
{
  call incr(n);
  call incr(n);
}
