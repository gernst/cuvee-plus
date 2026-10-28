// ./Cuvee.sh examples/dafny/language/choices.dfy
// guarded cases as a term, if { case p => x case q => y }, as the printer writes the cases of an update outside of a
// combinator, e.g. in a remaining goal; a single case with the guard true is its result
function sign(x: int): int
{
  if {
    case x < 0 => -1
    case x == 0 => 0
    case 0 < x => 1
  }
}

function bounded(x: int, y: int): bool
{
  if { case x <= y => x } + 1 <= y + 1
}

// a set as the test of a conditional is not a choice
function member(s: set<int>): int
{
  if {1} <= s then 1 else 0
}
