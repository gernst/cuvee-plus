// ./Cuvee.sh -teq -include teq:aggregation -include teq:arrays -prove examples/c/teq/xor_aggregate_wrong.c
// the same with a rotation that stores the new first element at the end instead of the old one, which is no
// permutation: the goal of the rotation remains
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);
int bxor(int x[10])
{
  int i;
  int res;
  res = x[0];
  for (i = 1; i < 10; i++) {
    res = res ^ x[i];
  }
  return res;
}
int main()
{
  int x[10];
  int temp;
  for (int i = 0; i < 10; i++) {
    x[i] = __VERIFIER_nondet_int();
  }
  int r = bxor(x);
  temp = x[0]; x[0] = x[1]; x[1] = temp;
  int r2 = bxor(x);
  temp = x[0];
  for (int i = 0; i < 9; i++) {
    x[i] = x[i + 1];
  }
  x[9] = x[0];
  int r5 = bxor(x);
  if (r != r2 || r != r5) { reach_error(); }
  return 1;
}
