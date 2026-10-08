// ./Cuvee.sh -simplify -chc examples/c/horn/invalid_count.c
// expected: invalid
// the loop counts only every second iteration

int main(void)
{
  int n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < n);
  int k = 0;
  int i = 0;
  while (i < n) {
    i += 2;
    k++;
  }
  assert(k == n);
  return 0;
}
