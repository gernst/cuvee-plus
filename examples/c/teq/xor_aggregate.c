// ./Cuvee.sh -teq -include teq:aggregation -include teq:arrays -prove examples/c/teq/xor_aggregate.c
// the bitwise exclusive disjunction of an array is the same after a swap and a rotation (xor1 to xor4 of SV-COMP,
// array-crafted): the fold bxors from the first element, absorbed into the aggregate of all elements
// (bxor_seed_selects, bxor_seed_earlier), whose multiset the permutations keep (elems_selects_swap,
// elems_selects_rotate)
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
  x[9] = temp;
  int r5 = bxor(x);
  if (r != r2 || r != r5) { reach_error(); }
  return 1;
}
