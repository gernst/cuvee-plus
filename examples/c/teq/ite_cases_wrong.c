// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/ite_cases_wrong.c
// the same with a wrong assertion: all values may be at most 0, which must leave a goal
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[100];
  int i;
  for (i = 0; i < 100; i++) { a[i] = __VERIFIER_nondet_int(); }
  int ret = 0;
  for (i = 0; i < 100; i++) { ret = ret < a[i] ? a[i] : ret; }
  __VERIFIER_assert(1 <= ret);
  return 0;
}
