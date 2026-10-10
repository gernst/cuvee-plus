// ./Cuvee.sh examples/dafny/parsing/keyword_const.dfy
// const is a name of a function, as const of the prelude of C in the output of -print dfy, like map and multiset
function const<a₀, a₁>(x₀: a₁): array<a₀, a₁>

function zeros(): array<int, int> { const(0) }
