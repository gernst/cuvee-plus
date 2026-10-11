// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/data_structures_set_multi_proc_trivial_ground.c
// SV-COMP array-examples/data_structures_set_multi_proc_trivial_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/data_structures_set_multi_proc_trivial_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "data_structures_set_multi_proc_trivial_ground.c", 7, "reach_error"); }
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

int insert(int Set[], int size, int value) {
  int result = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && size < N && N <= 536870911);
  int set_1[N];
  set_1 = Set;
  set_1[size] = value;
  result = size + 1;
  return result;
}

int elem_exists(int Set[], int size, int value) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
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
  int result = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  int tmp_4 = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  int Set[N];
  int values[N];
  assume_abort_if_not(0 < N);
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
      __VERIFIER_assert(Set[x] != Set[y]);
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
    if (tmp_4 != 0) {
      n = insert(Set, n, values[v]);
    }
    x = 0;
    while (x < n) {
      y = x + 1;
      while (y < n) {
        __VERIFIER_assert(Set[x] != Set[y]);
        y = y + 1;
      }
      x = x + 1;
    }
    v = v + 1;
  }
  x = 0;
  while (x < n) {
    y = x + 1;
    while (y < n) {
      __VERIFIER_assert(Set[x] != Set[y]);
      y = y + 1;
    }
    x = x + 1;
  }
  result = 0;
  return result;
}

