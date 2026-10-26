// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/copy_prefix.c
// a copy of the values that a loop stores, read after the loops (standard_copy1_ground): the copy reads the values as
// the prefix of their list (maps_earlier), the assertion reads the list, which earlier_prefix connects
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int b[1000];
  int i;
  for (i = 0; i < 1000; i++) { a[i] = __VERIFIER_nondet_int(); }
  for (i = 0; i < 1000; i++) { b[i] = a[i]; }
  int x = __VERIFIER_nondet_int();
  if (0 <= x && x < 1000) { __VERIFIER_assert(a[x] == b[x]); }
  return 0;
}
