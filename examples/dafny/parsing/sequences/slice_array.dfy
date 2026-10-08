// ./Cuvee.sh -print null examples/dafny/parsing/sequences/slice_array.dfy
function f(a: array<int,int>): bool { a[1..] == a }
