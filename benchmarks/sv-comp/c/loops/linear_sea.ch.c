// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/linear_sea.ch.c
// SV-COMP loops/linear_sea.ch.yml, translated from benchmarks/sv-comp/dafny/loops/linear_sea.ch.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "linear_sea.ch.c", 7, "reach_error"); }
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

int linear_search(int a[], int n, int q) {
  int result = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  j = 0;
  while (j < n && a[j] != q) {
    j = j + 1;
  }
  if (j < SIZE) {
    result = 1;
    return result;
  } else {
    result = 0;
    return result;
  }
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  SIZE = tmp_1 / 8 + 1;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && SIZE / 2 < N && SIZE <= N && 3 <= N && N <= 536870911);
  int a[N];
  if (SIZE > 1) {
    a[SIZE / 2] = 3;
    tmp_2 = linear_search(a, SIZE, 3);
    __VERIFIER_assert(tmp_2 != 0);
  }
}

