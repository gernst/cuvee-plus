// ./Cuvee.sh -vcgen -z3 examples/c/vcgen/acsl_loopentry.c
// \at(e, LoopEntry) under a quantifier: the quantified variable k is not copied at the entry of the loop, only the
// variables of the program, here the array x, which the loop rotates
int main(void) {
  int x[10];
  int temp = x[0];
  /*@ loop invariant 0 <= i <= 9;
      loop invariant \forall integer k; 0 <= k < i ==> x[k] == \at(x[k+1], LoopEntry);
      loop invariant \forall integer k; i <= k < 10 ==> x[k] == \at(x[k], LoopEntry);
      loop invariant temp == \at(x[0], LoopEntry); */
  for (int i = 0; i < 9; i++) {
    x[i] = x[i+1];
  }
  //@ assert x[8] == temp || x[8] != temp;
  x[9] = temp;
  return 0;
}
