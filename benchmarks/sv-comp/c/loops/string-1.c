// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/string-1.c
// SV-COMP loops/string-1.yml, translated from benchmarks/sv-comp/dafny/loops/string-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "string-1.c", 7, "reach_error"); }
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
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int nc_A = __VERIFIER_nondet_int();
  int nc_B = __VERIFIER_nondet_int();
  int found = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  assume_abort_if_not(0 < N);
  int string_A[N], string_B[N];
  found = 0;
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    string_A[i] = tmp_1;
    i = i + 1;
  }
  if (string_A[N - 1] != 0) {
    result = 0;
    return result;
  }
  i = 0;
  while (i < N) {
    tmp_2 = __VERIFIER_nondet_int();
    string_B[i] = tmp_2;
    i = i + 1;
  }
  if (string_B[N - 1] != 0) {
    result = 0;
    return result;
  }
  nc_A = 0;
  while (string_A[nc_A] != 0) {
    nc_A = nc_A + 1;
  }
  nc_B = 0;
  while (string_B[nc_B] != 0) {
    nc_B = nc_B + 1;
  }
  if (!(nc_B >= nc_A)) {
    result = 0;
    return result;
  }
  j = 0;
  i = j;
  while (i < nc_A && j < nc_B) {
    if (string_A[i] == string_B[j]) {
      i = i + 1;
      j = j + 1;
    } else {
      i = i - j + 1;
      j = 0;
    }
  }
  found = j > nc_B - 1 ? 1 : 0;
  __VERIFIER_assert(found == 0 || found == 1);
  result = 0;
  return result;
}

