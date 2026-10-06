// expected: valid
// global variables, which procedures and loops declare as modified, verified with -chc,
// where the predicates of procedures with a body replace their contracts

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
  if (0 <= counter && counter <= limit) {
    while (counter < limit)
      modifies counter;
    {
      call incr();
    }
    assert counter == limit;
  }
}
