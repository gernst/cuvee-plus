// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-industry-pattern/array_of_struct_ptr_monotonic.c
// SV-COMP array-industry-pattern/array_of_struct_ptr_monotonic.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_of_struct_ptr_monotonic.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_of_struct_ptr_monotonic.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
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
  int i = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  _Bool y = __VERIFIER_nondet_bool();
  assume_abort_if_not(0 <= N && N <= 268435455);
  assume_abort_if_not(0 < N);
  int t[N];
  _Bool p1[N];
  i = 0;
  while (i < N) {
    x = __VERIFIER_nondet_int();
    t[i] = x;
    if (x == 10) {
      p1[i] = 1;
    } else {
      y = __VERIFIER_nondet_bool();
      p1[i] = y;
    }
    i = i + 2;
  }
  i = 0;
  while (i < N) {
    if (t[i] == 10) {
      __VERIFIER_assert(p1[i]);
    }
    i = i + 2;
  }
}

