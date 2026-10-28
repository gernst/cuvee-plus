procedure main(a: [int]int, alength: int)
  returns (b: [int]int, blength: int)
  requires 0 <= alength;
  ensures (forall k: int ::
    (1 <= alength && 0 <= k && k < alength &&
      (forall l: int :: 0 <= l && l < k ==> a[k] == a[l])) ==>
        (exists j: int :: 0 <= j && j < blength && a[k] == b[j]));
  ensures (forall j: int :: (exists k: int ::
    1 <= alength && 0 <= j && j < blength ==>
      0 <= k && k < alength && b[j] == a[k]));
  ensures (forall j: int, k: int ::
    1 <= alength && 0 <= j && 0 <= k && j <= k && k < blength ==>
      b[k] <= b[j]);
{
	var i: int;
	var m: int;
	b := b[0 := a[0]];
	blength := 1;

	i := 0;
	m := 0;
	while (i < alength)
	{
		if (a[i] < a[m])
		{
			b := b[i := a[i]];
			blength := blength + 1;
			m := i;
		}
		else
		{
		}
		i := i + 1;
	}
}
