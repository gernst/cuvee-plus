// ./Cuvee.sh -teq -prove examples/c/teq/floats_nan.c
// a property of the floating point numbers themselves is not proved: d == d does not hold for NaN, the comparison is
// a declared function (c.Parser.floats)
extern double __VERIFIER_nondet_double(void);
int main(void) {
  double d = __VERIFIER_nondet_double();
  assert(d == d);
  return 0;
}
