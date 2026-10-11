// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array23_pattern.c
// SV-COMP array-patterns/array23_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array23_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array23_pattern.c", 7, "reach_error"); }
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

int outerBoundaryPatternCheck(int index) {
  int result = __VERIFIER_nondet_int();
  if (index == 0 || index == ARR_SIZE - 1) {
    result = 1;
    return result;
  } else {
    result = 0;
    return result;
  }
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  int row = __VERIFIER_nondet_int();
  int column = __VERIFIER_nondet_int();
  int num = __VERIFIER_nondet_int();
  int sum = __VERIFIER_nondet_int();
  int temp = __VERIFIER_nondet_int();
  int index1 = __VERIFIER_nondet_int();
  int index2 = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  ARR_SIZE = tmp_1;
  assume_abort_if_not(ARR_SIZE > 1);
  row = 0;
  column = 0;
  num = -1;
  sum = 0;
  row = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && ARR_SIZE <= N && N <= 16383);
  int Array[N][N];
  while (row < ARR_SIZE) {
    column = 0;
    while (column < ARR_SIZE) {
      Array[row][column] = 0;
      column = column + 1;
    }
    row = row + 1;
  }
  while (1 != 0) {
    index1 = __VERIFIER_nondet_int();
    index2 = __VERIFIER_nondet_int();
    assume_abort_if_not(index1 >= 0 && index1 < ARR_SIZE);
    assume_abort_if_not(index2 >= 0 && index2 < ARR_SIZE);
    tmp_2 = outerBoundaryPatternCheck(index1);
    Array[index1][index2] = tmp_2 != 0 ? num * num : Array[index1][index2];
    tmp_3 = outerBoundaryPatternCheck(index1);
    Array[ARR_SIZE - 1 - index1][index2] =
      tmp_3 != 0 ? num : Array[ARR_SIZE - 1 - index1][index2];
    temp = __VERIFIER_nondet_int();
    if (temp == 0) {
      break;
    }
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
  __VERIFIER_assert(sum == 0);
  result = 0;
  return result;
}

