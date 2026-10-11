// ./Cuvee.sh -teq -simplify -split -simplify examples/c/teq/unsigned_parity.c
// an unsigned counter by 2 without a bound, whose values wrap around, but stay even, since 2 divides 2^32
extern int __VERIFIER_nondet_int(void);
int main(void) { unsigned int x = 0;
  while (__VERIFIER_nondet_int()) { x = x + 2; }
  assert(x % 2 == 0); return 0; }
