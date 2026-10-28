procedure main(alength: int, v: int)
  returns (a: [int]int)
  requires 0 <= alength;
  ensures (forall pos: int :: 0 <= pos && pos < alength && 0 <= alength ==>
    a[pos] == v);
{
	var i: int;
	i := 0;
	while(i < alength)
	{
		a := a[i := v];
		i := i + 1;
	}
}
