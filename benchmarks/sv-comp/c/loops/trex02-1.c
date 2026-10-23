// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops/trex02-1.c
// SV-COMP loops/trex02-1.yml, translated from benchmarks/sv-comp/dafny/loops/trex02-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "trex02-1.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int x;

void foo(void) {
  x = x - 1;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  _Bool tmp_1 = __VERIFIER_nondet_bool();
  _Bool c = __VERIFIER_nondet_bool();
  x = __VERIFIER_nondet_int();
  while (x > 0) {
    tmp_1 = __VERIFIER_nondet_bool();
    c = tmp_1;
    if (c) {
      foo();
    } else {
      foo();
    }
  }
  __VERIFIER_assert(x <= 0);
}

