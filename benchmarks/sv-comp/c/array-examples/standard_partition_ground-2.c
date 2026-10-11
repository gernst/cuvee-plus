// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_partition_ground-2.c
// SV-COMP array-examples/standard_partition_ground-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_partition_ground-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_partition_ground-2.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int tmp = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 134217727);
  int aa[N];
  int bb[N];
  int cc[N];
  assume_abort_if_not(0 < N);
  a = 0;
  b = 0;
  c = 0;
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    aa[i] = tmp;
    i = i + 1;
  }
  while (a < N) {
    if (aa[a] >= 0) {
      bb[b] = aa[a];
      b = b + 1;
    }
    a = a + 1;
  }
  a = 0;
  while (a < N) {
    if (aa[a] < 0) {
      cc[c] = aa[a];
      c = c + 1;
    }
    a = a + 1;
  }
  x = 0;
  while (x < b) {
    __VERIFIER_assert(bb[x] >= 0);
    x = x + 1;
  }
}

