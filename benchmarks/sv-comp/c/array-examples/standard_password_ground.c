// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/array-examples/standard_password_ground.c
// SV-COMP array-examples/standard_password_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_password_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_password_ground.c", 7, "reach_error"); }
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

void main(void) {
  int N = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  int result = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  int password[N];
  int guess[N];
  assume_abort_if_not(0 < N);
  result = 1;
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    password[i] = v;
    v = __VERIFIER_nondet_int();
    guess[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    if (password[i] != guess[i]) {
      result = 0;
    }
    i = i + 1;
  }
  if (result != 0) {
    x = 0;
    while (x < N) {
      __VERIFIER_assert(password[x] == guess[x]);
      x = x + 1;
    }
  }
}

