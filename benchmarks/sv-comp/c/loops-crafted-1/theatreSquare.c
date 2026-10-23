// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops-crafted-1/theatreSquare.c
// SV-COMP loops-crafted-1/theatreSquare.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/theatreSquare.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "theatreSquare.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int correct_version(int n, int m, int a) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int l = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  i = 0;
  j = 0;
  b = 0;
  l = 0;
  while (b < n) {
    b = b + a;
    i = i + 1;
  }
  while (l < m) {
    l = l + a;
    j = j + 1;
  }
  x = 0;
  y = 0;
  while (x < i) {
    y = y + j;
    x = x + 1;
  }
  result = y;
  return result;
}

int student_version(int n, int m, int a) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int l = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  i = 0;
  j = 0;
  b = 0;
  l = 0;
  while (b < n) {
    b = b + a;
    i = i + 1;
  }
  while (l < m) {
    l = l + a;
    j = j + 1;
  }
  x = 0;
  y = 0;
  while (x < i) {
    y = y + j;
    x = x + 1;
  }
  result = y;
  return result;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  int tmp_4 = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int m = __VERIFIER_nondet_int();
  int n_stones1 = __VERIFIER_nondet_int();
  int n_stones2 = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  a = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  n = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  m = tmp_3;
  tmp_4 = __VERIFIER_nondet_int();
  n_stones2 = tmp_4;
  n_stones1 = n_stones2;
  if (1 <= n && 1 <= m && 1 <= a && n <= 109 && m <= 109 && a <= 109) {
    n_stones1 = correct_version(n, m, a);
    n_stones2 = student_version(n, m, a);
  }
  __VERIFIER_assert(n_stones1 == n_stones2);
  result = 0;
  return result;
}

