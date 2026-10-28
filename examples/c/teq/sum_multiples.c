// ./Cuvee.sh -teq -include teq:aggregation -prove examples/c/teq/sum_multiples.c
// a sum of the steps 6 or 3 is a multiple of 3, also in the negative case of the remainder of C, which cannot occur,
// since the sum is not negative (loopv1 of SV-COMP: sum_mod_multiples and sum_above of teq:aggregation)
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
  __VERIFIER_assert(i % 3 == 0);
  return 0;
}
