// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-crafted/simple_array_index_value_2.c
// SV-COMP loop-crafted/simple_array_index_value_2.yml, translated from benchmarks/sv-comp/dafny/loop-crafted/simple_array_index_value_2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "simple_array_index_value_2.c", 7, "reach_error"); }
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
  int N = __VERIFIER_nondet_int();
  int index = __VERIFIER_nondet_int();
  int tmp = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int Array[N];
  assume_abort_if_not(0 < N);
  index = 0;
  while (index < N) {
    tmp = __VERIFIER_nondet_int();
    assume_abort_if_not(tmp > index);
    Array[index] = tmp;
    index = index + 1;
  }
  index = 0;
  while (index < N) {
    __VERIFIER_assert(Array[index] > index);
    index = index + 1;
  }
}

