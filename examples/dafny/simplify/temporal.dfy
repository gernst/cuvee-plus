// ./Cuvee.sh -simplify examples/dafny/simplify/temporal.dfy
// facts hold now, and the engine does not know which variables change from state to state, hence x == 0 is not
// used inside of always (conservative for the bound x, which is the same at all states); the operands are simplified
// on their own
goal forall x: int :: x == 0 ==> always x == 0
goal forall x: int :: x == 0 && always (x + 1 > x && x == 0) ==> eventually x == 0
