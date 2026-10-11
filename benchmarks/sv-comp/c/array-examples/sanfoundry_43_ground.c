// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/sanfoundry_43_ground.c
// SV-COMP array-examples/sanfoundry_43_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/sanfoundry_43_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sanfoundry_43_ground.c", 7, "reach_error"); }
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

void incrementArray(int src[], int dst[], int N) {
  assume_abort_if_not(0 <= N && N <= 536870911);
  int dst_1[N];
  int i = __VERIFIER_nondet_int();
  dst_1 = dst;
  i = 0;
  while (i < N) {
    dst_1[i] = src[i] + 1;
    i = i + 1;
  }
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  int src[N];
  int dst[N];
  assume_abort_if_not(0 < N);
  i = 0;
  while (i < N) {
    tmp_2 = __VERIFIER_nondet_int();
    src[i] = tmp_2;
    i = i + 1;
  }
  incrementArray(src, dst, N);
  x = 0;
  while (x < N) {
    src[x] = dst[x] - 1;
    x = x + 1;
  }
  result = 0;
  return result;
}

