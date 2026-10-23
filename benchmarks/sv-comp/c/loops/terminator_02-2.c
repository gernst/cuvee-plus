// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops/terminator_02-2.c
// SV-COMP loops/terminator_02-2.yml, translated from benchmarks/sv-comp/dafny/loops/terminator_02-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "terminator_02-2.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
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
  _Bool tmp_3 = __VERIFIER_nondet_bool();
  int x = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  _Bool tmp = __VERIFIER_nondet_bool();
  assume_abort_if_not(0 < N);
  tmp_1 = __VERIFIER_nondet_int();
  x = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  z = tmp_2;
  if (!(x > -N)) {
    result = 0;
    return result;
  }
  if (!(z > N)) {
    result = 0;
    return result;
  }
  while (x < N && z > N) {
    tmp_3 = __VERIFIER_nondet_bool();
    tmp = tmp_3;
    if (tmp) {
      x = x + 1;
    } else {
      x = x - 1;
      z = z - 1;
    }
  }
  __VERIFIER_assert(x >= N || z <= N);
  result = 0;
  return result;
}

