// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-acceleration/simple_4-2.c
// SV-COMP loop-acceleration/simple_4-2.yml, translated from benchmarks/sv-comp/dafny/loop-acceleration/simple_4-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "simple_4-2.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int x = __VERIFIER_nondet_int();
  x = 268435440;
  while (x > 0) {
    x = x - 2;
  }
  __VERIFIER_assert(x % 2 == 0);
}

