// ./Cuvee.sh -teq -include teq:aggregation -include teq:arrays -prove examples/c/teq/bit_aggregates_wrong.c
// the same with a rotation that stores the new first element at the end instead of the old one, which is no
// permutation: the goals of the rotation remain
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);
int band(int x[10])
{
  int i;
  int res;
  res = x[0];
  for (i = 1; i < 10; i++) {
    res = res & x[i];
  }
  return res;
}
int bor(int x[10])
{
  int i;
  int res;
  res = x[0];
  for (i = 1; i < 10; i++) {
    res = res | x[i];
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
  int a = band(x);
  int o = bor(x);
  temp = x[0]; x[0] = x[1]; x[1] = temp;
  int a2 = band(x);
  int o2 = bor(x);
  temp = x[0];
  for (int i = 0; i < 9; i++) {
    x[i] = x[i + 1];
  }
  x[9] = x[0];
  int a5 = band(x);
  int o5 = bor(x);
  if (a != a2 || a != a5 || o != o2 || o != o5) { reach_error(); }
  return 1;
}
