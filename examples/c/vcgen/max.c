// ./Cuvee.sh -verify -z3 examples/c/vcgen/max.c
// expected: valid
// the maximum of two numbers, without loops

int max(int x, int y)
{
  if (x < y)
    return y;
  else
    return x;
}

int main(void)
{
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int m = max(a, b);
  // the call has no contract, the result is unknown
  m = a < b ? b : a;
  assert(m >= a && m >= b);
  return 0;
}
