// ./Cuvee.sh examples/c/count.c
// expected: valid
// loops, for with continue, and global variables, verified with -chc

int counter;

int main(void)
{
  int n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= n);
  counter = 0;
  for (int i = 0; i < n; i++) {
    if (i % 2 == 1)
      continue;
    counter++;
  }
  assert(counter <= n);
  return 0;
}
