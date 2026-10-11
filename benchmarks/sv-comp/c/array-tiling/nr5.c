// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/nr5.c
// SV-COMP array-tiling/nr5.yml, translated from benchmarks/sv-comp/dafny/array-tiling/nr5.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nr5.c", 7, "reach_error"); }
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
  int DEFAULTVALUE = __VERIFIER_nondet_int();
  int MINVAL = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  CELLCOUNT = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && CELLCOUNT / 5 < N && CELLCOUNT <= N && N <= 536870911);
  int volArray[N];
  if (CELLCOUNT > 1) {
    DEFAULTVALUE = 1;
    MINVAL = 2;
    if (CELLCOUNT % 5 != 0) {
      result = 1;
      return result;
    }
    assume_abort_if_not(CELLCOUNT % 5 == 0);
    i = 1;
    while (i <= CELLCOUNT / 5) {
      j = 5;
      while (j >= 1) {
        if (j >= MINVAL) {
          volArray[i * 5 - j] = j;
        } else {
          volArray[i * 5 - j] = 0;
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

