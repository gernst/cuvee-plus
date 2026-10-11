// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sorting_selectionsort_ground-2.c
// SV-COMP array-examples/sorting_selectionsort_ground-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/sorting_selectionsort_ground-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sorting_selectionsort_ground-2.c", 7, "reach_error"); }
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

int main(void) {
  int result = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int i_1 = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int s = __VERIFIER_nondet_int();
  int tmp = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int a[N];
  assume_abort_if_not(0 < N);
  i = 0;
  i_1 = 0;
  while (i_1 < N) {
    tmp_2 = __VERIFIER_nondet_int();
    a[i_1] = tmp_2;
    i_1 = i_1 + 1;
  }
  i = 0;
  while (i < N) {
    k = i + 1;
    s = i;
    while (k < N) {
      if (a[k] < a[s]) {
        s = k;
      }
      k = k + 1;
    }
    if (s != i) {
      tmp = a[s];
      a[s] = a[i];
      a[i] = tmp;
    }
    x = 0;
    while (x < i) {
      y = x + 1;
      while (y < i) {
        __VERIFIER_assert(a[x] <= a[y]);
        y = y + 1;
      }
      x = x + 1;
    }
    x = i;
    while (x < N) {
      __VERIFIER_assert(a[x] >= a[i]);
      x = x + 1;
    }
    i = i + 1;
  }
  x = 0;
  while (x < N) {
    y = x + 1;
    while (y < N) {
      __VERIFIER_assert(a[x] <= a[y]);
      y = y + 1;
    }
    x = x + 1;
  }
  result = 0;
  return result;
}

