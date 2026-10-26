// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/filters_wrong.c
// the same with a wrong assertion: the position nb is not written, which must leave a goal
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int b[1000];
  int c[1000];
  int nb = 0;
  int nc = 0;
  int i;
  for (i = 0; i < 1000; i++) { a[i] = __VERIFIER_nondet_int(); }
  for (i = 0; i < 1000; i++) {
    if (a[i] >= 0) {
      b[nb] = a[i];
      nb = nb + 1;
    } else {
      c[nc] = a[i];
      nc = nc + 1;
    }
  }
  int x = __VERIFIER_nondet_int();
  if (0 <= x && x <= nb) { __VERIFIER_assert(b[x] >= 0); }
  return 0;
}
