// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array24_pattern.c
// SV-COMP array-patterns/array24_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array24_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ARR_SIZE;

int outerBoundaryPatternCheck(int index) {
  int result;
  if (index == 0 || index == ARR_SIZE - 1) {
    result = 1;
    return result;
  } else {
    result = 0;
    return result;
  }
}

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  _Bool tmp_4;
  int Array[][];
  int row;
  int column;
  int num;
  int sum;
  int temp;
  int index1;
  int index2;
  tmp_1 = __VERIFIER_nondet_int();
  ARR_SIZE = tmp_1;
  __VERIFIER_assume(ARR_SIZE > 1);
  row = 0;
  column = 0;
  num = -1;
  sum = 0;
  row = 0;
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
    __VERIFIER_assume(index1 >= 0 && index1 < ARR_SIZE);
    __VERIFIER_assume(index2 >= 0 && index2 < ARR_SIZE);
    tmp_2 = outerBoundaryPatternCheck(index1);
    if (tmp_2 != 0) {
      tmp_4 = true;
    } else {
      tmp_3 = outerBoundaryPatternCheck(index2);
      tmp_4 = tmp_3 != 0;
    }
    Array[index1][index2] = tmp_4 ? Array[index1][index2] : num * num;
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
  assert(sum >= 0 && sum <= (ARR_SIZE - 2) * (ARR_SIZE - 2));
  result = 0;
  return result;
}

