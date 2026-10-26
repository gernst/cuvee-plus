// ./Cuvee.sh -teq -include teq:aggregation -prove examples/dafny/teq/unreachable.dfy
// unreachable positions are dropped (doc/prove.md): a combinator without iterations is empty, and the definitions by a
// match of the database are rules, which evaluate it

function g(z: int): int

lemma current_stop_example(w: int)
  ensures current(stop(w)) == w
{}

lemma butlast_stop_example(w: int)
  ensures ⌊stop(w)⌋ == nil
{}

// the body g(q) + 1 is never evaluated
lemma empty_map_example(m: int)
  requires m <= 0
  ensures sum(maps(for ⌊counter(0, 1, m)⌋ yield q :: g(q) + 1)) == 0
{}

// a loop whose test is false at the start
method empty_loop_example(m: int) returns (r: int)
  requires m <= 0
  ensures r == 7
{
  var i: int;
  i := 0;
  r := 7;
  while (i < m)
  {
    r := r + g(i);
    i := i + 1;
  }
}
