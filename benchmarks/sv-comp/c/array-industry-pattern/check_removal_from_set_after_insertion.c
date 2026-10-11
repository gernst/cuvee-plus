// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-industry-pattern/check_removal_from_set_after_insertion.c
// SV-COMP array-industry-pattern/check_removal_from_set_after_insertion.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/check_removal_from_set_after_insertion.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "check_removal_from_set_after_insertion.c", 7, "reach_error"); }
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

int SIZE;

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
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  int tmp_4 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int pos = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int found = __VERIFIER_nondet_int();
  int element = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  SIZE = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < SIZE);
  n = 0;
  found = 0;
  i = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && SIZE <= N && SIZE - 1 <= N && N <= 268435455);
  int Set[N];
  int values[N];
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
      __VERIFIER_assert(Set[i] != element);
      i = i + 1;
    }
  }
}

