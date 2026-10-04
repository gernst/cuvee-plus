// expected: valid
// loops, for with continue, and global variables modified by calls, verified with -chc

int counter;

void incr(void)
{
  counter++;
}

int main(void)
{
  int n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
  counter = 0;
  for (int i = 0; i < n; i++) {
    if (i % 2 == 1)
      continue;
    incr();
  }
  assert(counter <= n);
  return 0;
}
