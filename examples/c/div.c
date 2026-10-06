// expected: invalid
// division and remainder are translated to div and mod of SMT-LIB (see TODO.md),
// which round down for a positive divisor, whereas C truncates towards zero

int main(void)
{
  int x = -7;
  assert(x / 2 == -3);
  assert(x % 2 == -1);
  assert(7 / -2 == -3);
  assert(7 % -2 == 1);
  int y = __VERIFIER_nondet_int();
  __VERIFIER_assume(y != 0);
  assert((x / y) * y + x % y == x);
  return 0;
}
