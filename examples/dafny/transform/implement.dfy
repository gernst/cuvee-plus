// ./Cuvee.sh -include implement:listset -known implement -implement examples/dafny/transform/implement.dfy
// the functions on sets are replaced by those of the implementation listset, in programs, their contracts, and
// function bodies, with the arguments at the positions of the patterns, e.g. x in t by t.member(x)
function size(s: set<int>): int { |s| }

method add(s: set<int>, x: int) returns (t: set<int>, n: int)
  ensures x in t
  ensures n == size(t)
{
  t := s + {x};
  n := |t|;
}
