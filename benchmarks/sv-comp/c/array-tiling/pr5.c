// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/pr5.c
// SV-COMP array-tiling/pr5.yml, translated from benchmarks/sv-comp/dafny/array-tiling/pr5.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "pr5.c", 7, "reach_error"); }
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

int CELLCOUNT;

int main(void) {
  int result = __VERIFIER_nondet_int();
  int MINVAL = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int CCCELVOL5 = __VERIFIER_nondet_int();
  int CCCELVOL4 = __VERIFIER_nondet_int();
  int CCCELVOL3 = __VERIFIER_nondet_int();
  int CCCELVOL2 = __VERIFIER_nondet_int();
  int CCCELVOL1 = __VERIFIER_nondet_int();
  CELLCOUNT = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && CELLCOUNT / 5 < N && CELLCOUNT <= N && N <= 536870911);
  int volArray[N];
  if (CELLCOUNT > 1) {
    CCCELVOL5 = 2;
    CCCELVOL4 = 5;
    CCCELVOL3 = 7;
    CCCELVOL2 = 3;
    CCCELVOL1 = 1;
    if (CELLCOUNT % 5 != 0) {
      result = 1;
      return result;
    }
    assume_abort_if_not(CELLCOUNT % 5 == 0);
    i = 1;
    while (i <= CELLCOUNT / 5) {
      if (CCCELVOL5 >= MINVAL) {
        volArray[i * 5 - 5] = CCCELVOL5;
      } else {
        volArray[i * 5 - 5] = 0;
      }
      if (CCCELVOL4 >= MINVAL) {
        volArray[i * 5 - 4] = CCCELVOL4;
      } else {
        volArray[i * 5 - 4] = 0;
      }
      if (CCCELVOL3 >= MINVAL) {
        volArray[i * 5 - 3] = CCCELVOL3;
      } else {
        volArray[i * 5 - 3] = 0;
      }
      if (CCCELVOL2 >= MINVAL) {
        volArray[i * 5 - 2] = CCCELVOL2;
      } else {
        volArray[i * 5 - 2] = 0;
      }
      if (CCCELVOL1 >= MINVAL) {
        volArray[i * 5 - 1] = CCCELVOL1;
      } else {
        volArray[i * 5 - 1] = 0;
      }
      i = i + 1;
    }
    i = 0;
    while (i < CELLCOUNT) {
      __VERIFIER_assert(volArray[i] >= MINVAL || volArray[i] == 0);
      i = i + 1;
    }
  }
  result = 1;
  return result;
}

