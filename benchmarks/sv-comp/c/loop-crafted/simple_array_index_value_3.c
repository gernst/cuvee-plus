// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-crafted/simple_array_index_value_3.c
// SV-COMP loop-crafted/simple_array_index_value_3.yml, translated from benchmarks/sv-comp/dafny/loop-crafted/simple_array_index_value_3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "simple_array_index_value_3.c", 7, "reach_error"); }
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

void main(void) {
  int SIZE = __VERIFIER_nondet_int();
  int index = __VERIFIER_nondet_int();
  int tmp = __VERIFIER_nondet_int();
  SIZE = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < SIZE);
  index = 0;
  tmp = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && SIZE <= N && N <= 536870911);
  int Array[N];
  while (index < SIZE) {
    Array[index] = tmp;
    index = index + 1;
    tmp = tmp + 2;
  }
  index = 0;
  while (index < SIZE) {
    __VERIFIER_assert(Array[index] == 2 * index || Array[index] == 0);
    index = index + 1;
  }
}

