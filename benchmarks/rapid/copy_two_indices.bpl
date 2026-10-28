procedure main(b: [int]int, blength: int)
  returns (a: [int]int)
  requires 0 <= blength;
  ensures (forall k: int :: 0 <= blength && 0 <= k && k < blength ==>
    a[k] == b[k]);
{
	var i: int;
	var j: int;
	i := 0;
	j := 0;
	while(i < blength)
	{
		a := a[i := b[j]];
		i := i + 1;
		j := j + 1;
	}
}
