// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/compacts_wrong.c
// the same with a wrong assertion: the last of them may be the last iteration, which must leave a goal
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int a[1000];
  int b[1000];
  int c[1000];
  int i;
  int j = 0;
  for (i = 0; i < 1000; i++) {
    if (a[i] == b[i]) {
      c[j] = i;
      j = j + 1;
    }
  }
  int x = __VERIFIER_nondet_int();
  if (0 <= x && x < j) { __VERIFIER_assert(x <= c[x] && c[x] < x + i - j); }
  return 0;
}
