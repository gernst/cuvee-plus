// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array29_pattern.c
// SV-COMP array-patterns/array29_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array29_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ARR_SIZE;

int main(void) {
  int result;
  int tmp_1;
  int Array[][];
  int row;
  int column;
  int sum;
  tmp_1 = __VERIFIER_nondet_int();
  ARR_SIZE = tmp_1;
  __VERIFIER_assume(ARR_SIZE > 1);
  row = 0;
  column = 0;
  sum = 0;
  row = 0;
  while (row < ARR_SIZE) {
    column = 0;
    while (column < ARR_SIZE) {
      if (row == column) {
        Array[row][row] = 0;
      } else {
        Array[row][column] = column;
      }
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
  assert(2 * sum == ARR_SIZE * (ARR_SIZE - 1) * (ARR_SIZE - 1));
  result = 0;
  return result;
}

