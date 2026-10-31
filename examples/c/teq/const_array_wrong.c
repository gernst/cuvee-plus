// ./Cuvee.sh -teq -prove examples/c/teq/const_array_wrong.c
// the same with a read compared with another value than the one of the array: the goal remains
extern void abort(void);
void reach_error() { abort(); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: {reach_error(); abort();} } }
extern int __VERIFIER_nondet_int(void);
int a[1000];
int main()
{
  int n = __VERIFIER_nondet_int();
  for (int i = 0; i < n && i < 1000; i++) {
    __VERIFIER_assert(a[i] == 1);
  }
  return 0;
}
