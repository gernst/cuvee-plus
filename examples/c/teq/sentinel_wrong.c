// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/sentinel_wrong.c
// the same with a wrong assertion: the search may end at pos, which must leave a goal
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int marker = __VERIFIER_nondet_int();
  int pos = __VERIFIER_nondet_int();
  for (int i = 0; i < 1000; i++) { a[i] = __VERIFIER_nondet_int(); }
  if (pos >= 0 && pos < 1000) {
    a[pos] = marker;
    int i = 0;
    while (a[i] != marker) { i = i + 1; }
    __VERIFIER_assert(i < pos);
  }
  return 0;
}
