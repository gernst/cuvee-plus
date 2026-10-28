// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/stores_cases_point.c
// a copy whose iteration at the position z stores the same value by a branch of its own (copysome2-1): both branches
// store a[i] at i, the fold stores with the values per case (Rewrite.update), the keys stay the counter
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int b[1000];
  int i;
  int z = 500;
  for (i = 0; i < 1000; i++) { a[i] = __VERIFIER_nondet_int(); }
  for (i = 0; i < 1000; i++) {
    if (i != z) {
      b[i] = a[i];
    } else {
      b[i] = a[i];
    }
  }
  int x = __VERIFIER_nondet_int();
  if (0 <= x && x < 1000) { __VERIFIER_assert(a[x] == b[x]); }
  return 0;
}
