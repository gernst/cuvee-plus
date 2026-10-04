// expected: valid
// sequences: literals, concatenation, length, indexing, slices, membership and prefix

method cons(s: seq<int>, x: int) returns (t: seq<int>)
  ensures x in t && |t| == |s| + 1 && t[1..] == s && t[0] == x
  ensures [x] <= t && t[..1] == [x]
{
  t := [x] + s;
}
