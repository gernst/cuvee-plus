// ./Cuvee.sh -teq -prove examples/c/teq/floats.c
// floating point numbers as uninterpreted sorts with declared operations (c.Parser.floats), and sqrt of math.h as a
// declared function: a property of the integers holds whatever the doubles are (as in knuth of nla-digbench)
extern double sqrt(double);
extern double __VERIFIER_nondet_double(void);
int main(void) {
  double d = __VERIFIER_nondet_double();
  double s = sqrt(d) + 0.5;
  int i = 0; int n = 0;
  while (i < 10) { if (s < 2.0) { n = n + 1; } else { n = n + 2; } i = i + 1; }
  assert(n >= 10);
  return 0;
}
