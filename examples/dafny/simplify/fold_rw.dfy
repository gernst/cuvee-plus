// ./Cuvee.sh -prove examples/dafny/simplify/fold_rw.dfy
// a definition cannot be both unfolded and folded, which would loop
function {:rw} {:fold} twice(x: int): int
{
  x + x
}
