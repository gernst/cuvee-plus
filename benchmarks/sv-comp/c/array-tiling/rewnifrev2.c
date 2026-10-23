// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-tiling/rewnifrev2.c
// SV-COMP array-tiling/rewnifrev2.yml, translated from benchmarks/sv-comp/dafny/array-tiling/rewnifrev2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "rewnifrev2.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void assume_abort_if_not(int cond) {
  if (!cond) { abort(); }
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int SIZE;

int main(void) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  SIZE = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && SIZE <= N && N <= 536870911);
  int a[N];
  if (SIZE > 1) {
    i = SIZE - 2;
    while (i >= 0) {
      a[i] = i;
      a[i + 1] = i + 1;
      i = i - 1;
    }
    i = 0;
    while (i < SIZE) {
      __VERIFIER_assert(a[i] >= i);
      i = i + 1;
    }
  }
  result = 1;
  return result;
}

