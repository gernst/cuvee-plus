// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/ite_cases.c
// a maximum by a conditional expression (reducercommutativity/max*): the conditional in the update of the trace is
// lifted into cases, ret < a[i] => a[i] and a[i] <= ret => ret, which the fold maxs matches (Simplify.cases)
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
  __VERIFIER_assert(0 <= ret);
  return 0;
}
