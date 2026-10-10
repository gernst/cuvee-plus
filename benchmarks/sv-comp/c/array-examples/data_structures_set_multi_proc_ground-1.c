// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/data_structures_set_multi_proc_ground-1.c
// SV-COMP array-examples/data_structures_set_multi_proc_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/data_structures_set_multi_proc_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
      result = 0;
      return result;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

int main(void) {
  int result;
  int N;
  int tmp_2;
  int tmp_3;
  int tmp_4;
  int n;
  int Set[];
  int x;
  int y;
  int values[];
  int v;
  __VERIFIER_assume(0 < N);
  n = 0;
  x = 0;
  while (x < N) {
    tmp_2 = __VERIFIER_nondet_int();
    Set[x] = tmp_2;
    x = x + 1;
  }
  x = 0;
  while (x < n) {
    y = x + 1;
    while (y < n) {
      assert(Set[x] != Set[y]);
      y = y + 1;
    }
    x = x + 1;
  }
  v = 0;
  while (v < N) {
    tmp_3 = __VERIFIER_nondet_int();
    values[v] = tmp_3;
    v = v + 1;
  }
  v = 0;
  while (v < N) {
    tmp_4 = elem_exists(Set, n, values[v]);
    if (!(tmp_4 != 0)) {
      n = insert(Set, n, values[v]);
    }
    v = v + 1;
  }
  x = 0;
  while (x < n) {
    y = x + 1;
    while (y < n) {
      assert(Set[x] != Set[y]);
      y = y + 1;
    }
    x = x + 1;
  }
  result = 0;
  return result;
}

