// ./Cuvee.sh -teq -include teq:aggregation -include teq:arrays -prove examples/c/teq/sep_parity_wrong.c
// the same with a rotation that stores the new first element at the end instead of the old one, which is no
// permutation: the goal of the rotation remains
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);
int sep(int x[10])
{
  int ret = 0;
  for (int i = 0; i < 10; i++) {
    if (x[i] % 2 == 0) ret++; else ret--;
  }
  return ret;
}
int main()
{
  int x[10];
  int temp;
  for (int i = 0; i < 10; i++) {
    x[i] = __VERIFIER_nondet_int();
  }
  int ret = sep(x);
  temp = x[0]; x[0] = x[1]; x[1] = temp;
  int ret2 = sep(x);
  temp = x[0];
  for (int i = 0; i < 9; i++) {
    x[i] = x[i + 1];
  }
  x[9] = x[0];
  int ret5 = sep(x);
  if (ret != ret2 || ret != ret5) { reach_error(); }
  return 1;
}
