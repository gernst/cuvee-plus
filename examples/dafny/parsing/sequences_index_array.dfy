// ./Cuvee.sh -print null examples/dafny/parsing/sequences_index_array.dfy
function f(a: array<int,bool>, i: int): bool { a[i] && a[i := false] == a }
