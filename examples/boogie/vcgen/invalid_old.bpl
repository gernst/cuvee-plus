// ./Cuvee.sh -vcgen -monomorph -z3 examples/boogie/vcgen/invalid_old.bpl
// expected: invalid
// the value at the entry is not the current one

var counter: int;

procedure incr(n: int)
  requires 0 < n;
  ensures counter == old(counter);
  modifies counter;
{
  counter := counter + n;
}
