// ./Cuvee.sh -quiet examples/dafny/parsing/included/twice.dfy
// included by include.dfy, includes base.dfy of the same directory
include "base.dfy"

function twice(x: int): int { 2 * base(x) - 1 }
