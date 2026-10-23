// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-simple/nested_5.c
// SV-COMP loop-simple/nested_5.yml, translated from benchmarks/sv-comp/dafny/loop-simple/nested_5.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested_5.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  int d = __VERIFIER_nondet_int();
  int e = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < N);
  a = N;
  b = N;
  c = N;
  d = N;
  e = N;
  a = 0;
  while (a < N) {
    b = 0;
    while (b < N) {
      c = 0;
      while (c < N) {
        d = 0;
        while (d < N) {
          e = 0;
          while (e < N) {
            e = e + 1;
          }
          d = d + 1;
        }
        c = c + 1;
      }
      b = b + 1;
    }
    a = a + 1;
  }
  if (!(a == N && b == N && c == N && d == N && e == N)) {
    __VERIFIER_assert(0);
  }
  result = 1;
  return result;
}

