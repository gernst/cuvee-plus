// expected: valid
// division and remainder truncate towards zero

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
