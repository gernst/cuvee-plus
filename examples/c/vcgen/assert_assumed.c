// ./Cuvee.sh -vcgen -split -print smt2 examples/c/vcgen/assert_assumed.c
// an assertion is assumed once it is checked: the goals after it, also the separate ones of -split,
// have it as hypothesis, here x * x >= 0 in the goal of the second assertion
extern int __VERIFIER_nondet_int(void);

int main(void) {
  int x = __VERIFIER_nondet_int();
  //@ assert x * x >= 0;
  //@ assert x * x + 1 > 0;
  return 0;
}
