// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/invert_string-1.c
// SV-COMP loops/invert_string-1.yml, translated from benchmarks/sv-comp/dafny/loops/invert_string-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "invert_string-1.c", 7, "reach_error"); }
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
  int MAX = __VERIFIER_nondet_int();
  int cont = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  MAX = tmp_1;
  if (!(MAX > 0)) {
    assume_abort_if_not(0);
  }
  cont = 0;
  i = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && MAX <= N && MAX - 1 < N && 0 < N && N <= 268435455);
  int str1[N];
  int str2[N];
  while (i < MAX) {
    tmp_2 = __VERIFIER_nondet_int();
    str1[i] = tmp_2;
    i = i + 1;
  }
  str1[MAX - 1] = 0;
  j = 0;
  i = MAX - 1;
  while (i >= 0) {
    str2[j] = str1[0];
    j = j + 1;
    i = i - 1;
  }
  j = MAX - 1;
  i = 0;
  while (i < MAX) {
    __VERIFIER_assert(str1[i] == str2[j]);
    j = j - 1;
    i = i + 1;
  }
}

