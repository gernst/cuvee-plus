// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/loopv3.c
// SV-COMP loops-crafted-1/loopv3.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/loopv3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "loopv3.c", 7, "reach_error"); }
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

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  SIZE = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < SIZE);
  i = 0;
  j = 0;
  while (i < SIZE) {
    tmp_1 = __VERIFIER_nondet_int();
    if (tmp_1 != 0) {
      i = i + 8;
    } else {
      i = i + 4;
    }
  }
  j = i / 4;
  __VERIFIER_assert(j * 4 == i);
  result = 0;
  return result;
}

