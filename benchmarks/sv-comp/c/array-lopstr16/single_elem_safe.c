// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/single_elem_safe.c
// SV-COMP array-lopstr16/single_elem_safe.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/single_elem_safe.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "single_elem_safe.c", 7, "reach_error"); }
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
  int q = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  _Bool w = __VERIFIER_nondet_bool();
  assume_abort_if_not(0 <= N && N <= 268435455);
  _Bool s[N];
  int n[N];
  _Bool p[N];
  assume_abort_if_not(0 < N);
  i = 0;
  while (i < N) {
    q = __VERIFIER_nondet_int();
    if (q == 0) {
      s[i] = 1;
      n[i] = q % 2;
      if (n[i] == 0) {
        p[i] = 1;
      } else {
        p[i] = 0;
      }
    } else {
      s[i] = 0;
    }
    i = i + 1;
  }
  v = __VERIFIER_nondet_int();
  w = __VERIFIER_nondet_bool();
  s[3] = 1;
  n[3] = v;
  p[3] = w;
  i = 0;
  while (i < N) {
    if (i != 3 && s[i] && n[i] == 0) {
      __VERIFIER_assert(p[i]);
    }
    i = i + 1;
  }
}

