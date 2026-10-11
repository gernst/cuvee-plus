// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array30_pattern.c
// SV-COMP array-patterns/array30_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array30_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array30_pattern.c", 7, "reach_error"); }
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

int ARR_SIZE;

int diff(int idx1, int idx2) {
  int result = __VERIFIER_nondet_int();
  if (idx1 > idx2) {
    result = idx1 - idx2;
    return result;
  } else {
    result = idx2 - idx1;
    return result;
  }
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int row = __VERIFIER_nondet_int();
  int column = __VERIFIER_nondet_int();
  int sum = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  ARR_SIZE = tmp_1;
  assume_abort_if_not(ARR_SIZE > 0);
  row = 0;
  column = 0;
  sum = 0;
  row = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && ARR_SIZE <= N && N <= 16383);
  int Array[N][N];
  while (row < ARR_SIZE) {
    column = 0;
    while (column < ARR_SIZE) {
      tmp_2 = diff(row, column);
      Array[row][column] = tmp_2;
      column = column + 1;
    }
    row = row + 1;
  }
  row = 0;
  while (row < ARR_SIZE) {
    column = 0;
    while (column < ARR_SIZE) {
      sum = sum + Array[row][column];
      column = column + 1;
    }
    row = row + 1;
  }
  __VERIFIER_assert(3 * sum == ARR_SIZE * (ARR_SIZE - 1) * (ARR_SIZE + 1));
  result = 0;
  return result;
}

