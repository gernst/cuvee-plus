// ./Cuvee.sh -teq -include teq:aggregation -include teq:arrays -prove examples/c/teq/bit_aggregates.c
// the bitwise conjunction and disjunction of an array are the same after a swap and a rotation (bAnd1, bor1 of
// SV-COMP, reducercommutativity): the folds bands and bors from the first element, absorbed into the aggregate of all
// elements (band_seed_selects, band_seed_earlier), whose multiset the permutations keep (elems_selects_swap,
// elems_selects_rotate)
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
  x[9] = temp;
  int a5 = band(x);
  int o5 = bor(x);
  if (a != a2 || a != a5 || o != o2 || o != o5) { reach_error(); }
  return 1;
}
