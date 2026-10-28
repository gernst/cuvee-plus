// ./Cuvee.sh -teq -include teq:aggregation -include teq:arrays -prove examples/c/teq/sep_parity.c
// the number of even minus the number of odd elements of an array is the same after a swap and a rotation (sep05-1 of
// SV-COMP, reducercommutativity): the guard x[i] % 2 == 0 of the remainder of C is one equation in both branches of
// its sign (Simplify.eq), the sum of 1 and -1 is the parity of the values (sum_parity_indicator), whose multiset the
// permutations keep
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
  x[9] = temp;
  int ret5 = sep(x);
  if (ret != ret2 || ret != ret5) { reach_error(); }
  return 1;
}
