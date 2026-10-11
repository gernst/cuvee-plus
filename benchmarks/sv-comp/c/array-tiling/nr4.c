// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/nr4.c
// SV-COMP array-tiling/nr4.yml, translated from benchmarks/sv-comp/dafny/array-tiling/nr4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nr4.c", 7, "reach_error"); }
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
  int j = __VERIFIER_nondet_int();
  CELLCOUNT = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && CELLCOUNT / 4 < N && CELLCOUNT <= N && N <= 536870911);
  int volArray[N];
  if (CELLCOUNT > 1) {
    MINVAL = 2;
    if (CELLCOUNT % 4 != 0) {
      result = 1;
      return result;
    }
    assume_abort_if_not(CELLCOUNT % 4 == 0);
    i = 1;
    while (i <= CELLCOUNT / 4) {
      j = 4;
      while (j >= 1) {
        if (j >= MINVAL) {
          volArray[i * 4 - j] = j;
        } else {
          volArray[i * 4 - j] = 0;
        }
        j = j - 1;
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

