// ./Cuvee.sh -fuse examples/dafny/parsing/invalid_fuse.dfy
// a request of fusion needs a composition of two functions applied to variables
function inc(x: int): int {
  x + 1
}

fuse inc(inc(1)) = ???
