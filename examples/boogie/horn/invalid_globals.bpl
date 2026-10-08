// ./Cuvee.sh -chc -monomorph examples/boogie/horn/invalid_globals.bpl
// expected: invalid
// the loop may not be entered, then counter exceeds limit

var counter: int;
var limit: int;

procedure incr()
  modifies counter;
{
  counter := counter + 1;
}

procedure main()
  modifies counter;
{
  while (counter < limit)
    modifies counter;
  {
    call incr();
  }
  assert counter == limit;
}
