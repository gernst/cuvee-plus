// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array26_pattern.c
// SV-COMP array-patterns/array26_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array26_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ARR_SIZE;

int main(void) {
  int result;
  int tmp_1;
  int Array[][];
  int row;
  int column;
  int num;
  int value;
  int sum;
  tmp_1 = __VERIFIER_nondet_int();
  ARR_SIZE = tmp_1;
  __VERIFIER_assume(ARR_SIZE > 1);
  row = 0;
  column = 0;
  num = -1;
  value = 1;
  sum = 0;
  row = 0;
  while (row < ARR_SIZE) {
    column = 0;
    while (column < ARR_SIZE) {
      if (row % 2 == 0 && column % 2 == 0) {
        Array[row][column] = value;
        value = value * num;
      } else if (row % 2 == 1 && column % 2 == 1) {
        Array[row][column] = value;
        value = value * num;
      } else {
        Array[row][column] = 0;
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
  assert(sum == 0 || sum == 1);
  result = 0;
  return result;
}

