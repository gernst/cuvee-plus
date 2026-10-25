// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/maps_earlier_prefix.c
// the second loop sums N - 1 of the N values that the first loop stores, so s == -a[N-1] at the assertion: the reads
// of the second loop are the prefix of the values of the first one (maps_earlier), not all of them (bugs.md);
// the options of -svcomp without the witness
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int N = __VERIFIER_nondet_int();
  if (N > 1) {
    int a[N];
    int s = 0;
    int i;
    for (i = 0; i < N; i++) { a[i] = __VERIFIER_nondet_int(); }
    for (i = 0; i < N - 1; i++) { s = s + a[i]; }
    for (i = 0; i < N; i++) { s = s - a[i]; }
    __VERIFIER_assert(s == 0);
  }
  return 0;
}
