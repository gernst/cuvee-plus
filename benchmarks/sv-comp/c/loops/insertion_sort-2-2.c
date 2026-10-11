// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/insertion_sort-2-2.c
// SV-COMP loops/insertion_sort-2-2.yml, translated from benchmarks/sv-comp/dafny/loops/insertion_sort-2-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "insertion_sort-2-2.c", 7, "reach_error"); }
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
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int SIZE = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int key = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  SIZE = tmp_1;
  if (SIZE >= 1000000000) {
    result = 0;
    return result;
  }
  j = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && SIZE <= N && N <= 536870911);
  int v[N];
  while (j < SIZE) {
    tmp_2 = __VERIFIER_nondet_int();
    v[j] = tmp_2;
    j = j + 1;
  }
  j = 1;
  while (j < SIZE) {
    key = v[j];
    i = j - 1;
    while (i >= 0 && v[i] > key) {
      v[i + 1] = v[i];
      i = i - 1;
    }
    v[i + 1] = key;
    j = j + 1;
  }
  k = 1;
  while (k < SIZE) {
    __VERIFIER_assert(v[k - 1] <= v[k]);
    k = k + 1;
  }
  result = 0;
  return result;
}

