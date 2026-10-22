// ./Cuvee.sh -quiet examples/dafny/parsing/sequences_slice_array.dfy
function f(a: array<int,int>): bool { a[1..] == a }
