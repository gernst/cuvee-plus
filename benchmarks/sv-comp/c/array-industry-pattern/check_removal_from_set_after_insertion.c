// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-industry-pattern/check_removal_from_set_after_insertion.c
// SV-COMP array-industry-pattern/check_removal_from_set_after_insertion.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/check_removal_from_set_after_insertion.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int SIZE;

int insert(int Set[], int size, int value) {
  int result;
  int set_1[];
  set_1 = Set;
  set_1[size] = value;
  result = size + 1;
  return result;
}

int elem_exists(int Set[], int size, int value) {
  int result;
  int i;
  i = 0;
  while (i < size) {
    if (Set[i] == value) {
      result = 1;
      return result;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

int main(void) {
  int result;
  int tmp_2;
  int tmp_3;
  int tmp_4;
  int i;
  int pos;
  int n;
  int found;
  int Set[];
  int values[];
  int element;
  int v;
  SIZE = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < SIZE);
  n = 0;
  found = 0;
  i = 0;
  while (i < SIZE) {
    tmp_2 = __VERIFIER_nondet_int();
    Set[i] = tmp_2;
    tmp_3 = __VERIFIER_nondet_int();
    values[i] = tmp_3;
    i = i + 1;
  }
  element = __VERIFIER_nondet_int();
  v = 0;
  while (v < SIZE) {
    tmp_4 = elem_exists(Set, n, values[v]);
    if (tmp_4 != 1) {
      n = insert(Set, n, values[v]);
    }
    v = v + 1;
  }
  i = 0;
  while (i < SIZE && found != 1) {
    if (Set[i] == element) {
      found = 1;
      pos = i;
    }
    i = i + 1;
  }
  if (found == 1) {
    i = pos;
    while (i < SIZE - 1) {
      Set[i] = Set[i + 1];
      i = i + 1;
    }
  }
  if (found == 1) {
    i = 0;
    while (i < SIZE - 1) {
      assert(Set[i] != element);
      i = i + 1;
    }
  }
}

