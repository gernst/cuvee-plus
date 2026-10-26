// ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic -include teq:arrays -include teq:counters -include teq:search -include teq:sorted -include teq:strides -include teq:unsigned -include teq:series -prove -split -prove -split -prove -quiet examples/c/teq/rows_wrong.c
// the same with a wrong assertion: the row 100 is not initialized, which must leave a goal
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int main()
{
  int A[100][150];
  int C = __VERIFIER_nondet_int();
  int i = 0;
  while (i < 100) {
    int j = 0;
    while (j < 150) {
      A[i][j] = C;
      j = j + 1;
    }
    i = i + 1;
  }
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (0 <= x && x <= 100 && 0 <= y && y < 150) { __VERIFIER_assert(A[x][y] == C); }
  return 0;
}
