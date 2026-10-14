// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-crafted/simple_array_index_value_4.c
// SV-COMP loop-crafted/simple_array_index_value_4.yml, translated from benchmarks/sv-comp/dafny/loop-crafted/simple_array_index_value_4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "simple_array_index_value_4.c", 7, "reach_error"); }
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

int main(void) {
  int result = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int index1 = __VERIFIER_nondet_int();
  int index2 = __VERIFIER_nondet_int();
  int loop_entered = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  assume_abort_if_not(0 < N);
  int Array[N];
  loop_entered = 0;
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    assume_abort_if_not(0 <= tmp_1);
    Array[i] = tmp_1;
    i = i + 1;
  }
  index1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= index1);
  assume_abort_if_not(index1 < N);
  index2 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= index2);
  assume_abort_if_not(index2 < N);
  while (index1 < index2) {
    __VERIFIER_assert(index1 < N && index2 < N);
    assume_abort_if_not(Array[index1] == Array[index2]);
    index1 = index1 + 1;
    index2 = index2 - 1;
    loop_entered = 1;
  }
  if (loop_entered != 0) {
    while (index2 < index1) {
      __VERIFIER_assert(Array[index1] == Array[index2]);
      index2 = index2 + 1;
      index1 = index1 - 1;
    }
  }
}

