// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/copy_both_ends_wrong.c
// the same with a wrong assertion: the copy is compared at the next position, which must leave a goal
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
    if (0 <= x && x < 2 * s - 1) { __VERIFIER_assert(b[x] == a[x + 1]); }
  }
  return 0;
}
