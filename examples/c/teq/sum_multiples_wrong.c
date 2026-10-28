// ./Cuvee.sh -teq -include teq:aggregation -prove examples/c/teq/sum_multiples_wrong.c
// the same with a wrong assertion: a sum of 6 or 3 need not be a multiple of 6, which must remain
extern void abort(void);
void reach_error() { abort(); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) { if (!(cond)) { reach_error(); } }
int main()
{
  int n = __VERIFIER_nondet_int();
  int i = 0;
  while (i < n) {
    if (__VERIFIER_nondet_int()) i = i + 6; else i = i + 3;
  }
  __VERIFIER_assert(i % 6 == 0);
  return 0;
}
