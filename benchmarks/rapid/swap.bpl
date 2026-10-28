var a: [int]int;
var b: [int]int;

procedure main(length: int)
  requires 0 <= length;
  ensures (forall pos: int :: 0 <= length && 0 <= pos && pos < length ==>
    a[pos] == old(b)[pos]);
  ensures (forall pos: int :: 0 <= length && 0 <= pos && pos < length ==>
    b[pos] == old(a)[pos]);
  modifies a, b;
{
	var i: int;
	var current: int;
	i := 0;
	while(i < length)
		modifies a, b;
	{
		current := a[i];
		a := a[i := b[i]];
		b := b[i := current];
		i := i + 1;
	}
}
