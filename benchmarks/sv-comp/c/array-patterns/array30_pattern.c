// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array30_pattern.c
// SV-COMP array-patterns/array30_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array30_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ARR_SIZE;

int diff(int idx1, int idx2) {
  int result;
  if (idx1 > idx2) {
    result = idx1 - idx2;
    return result;
  } else {
    result = idx2 - idx1;
    return result;
  }
}

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int Array[][];
  int row;
  int column;
  int sum;
  tmp_1 = __VERIFIER_nondet_int();
  ARR_SIZE = tmp_1;
  __VERIFIER_assume(ARR_SIZE > 0);
  row = 0;
  column = 0;
  sum = 0;
  row = 0;
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
  assert(3 * sum == ARR_SIZE * (ARR_SIZE - 1) * (ARR_SIZE + 1));
  result = 0;
  return result;
}

