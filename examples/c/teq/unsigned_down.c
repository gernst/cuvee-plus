// ./Cuvee.sh -teq -simplify -split -simplify examples/c/teq/unsigned_down.c
// an unsigned counter down to 0 from a nondeterministic value, x - 1 as x + 4294967295 modulo 2^32, and a counter up
// in parallel, which ends at the initial value
extern unsigned int __VERIFIER_nondet_uint(void);
int main(void) { unsigned int n = __VERIFIER_nondet_uint(); unsigned int x = n; unsigned int y = 0;
  while (x > 0) { x = x - 1; y = y + 1; }
  assert(y == n); return 0; }
