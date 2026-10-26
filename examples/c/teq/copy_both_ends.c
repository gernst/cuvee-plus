// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/copy_both_ends.c
// a copy from both ends (array-tiling/tcpy, array-cav19/array_tiling_tcpy): each covered position holds the value of the
// source (select_current_trace_copy_both_ends)
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int s = __VERIFIER_nondet_int();
  if (1 < s && s < 100000) {
    int a[2 * s];
    int b[2 * s];
    int i;
    for (i = 0; i < s; i++) {
      b[2 * s - (i + 1)] = a[2 * s - (i + 1)];
      b[i] = a[i];
    }
    int x = __VERIFIER_nondet_int();
    if (0 <= x && x < 2 * s) { __VERIFIER_assert(b[x] == a[x]); }
  }
  return 0;
}
