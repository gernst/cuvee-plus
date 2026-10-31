// ./Cuvee.sh -teq -prove examples/c/teq/const_array.c
// a global array is zero-initialized, the constant array const(0), whose reads are its value (select_const; lcp,
// elimination_max, nec40 of SV-COMP)
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int a[1000];
int main()
{
  int n = __VERIFIER_nondet_int();
  for (int i = 0; i < n && i < 1000; i++) {
    __VERIFIER_assert(a[i] == a[999 - i]);
  }
  return 0;
}
