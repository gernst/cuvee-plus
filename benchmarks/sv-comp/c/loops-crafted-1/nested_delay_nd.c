// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops-crafted-1/nested_delay_nd.c
// SV-COMP loops-crafted-1/nested_delay_nd.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/nested_delay_nd.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "nested_delay_nd.c", 7, "reach_error"); }
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

int last;

int SIZE;

int main(void) {
  int result = __VERIFIER_nondet_int();
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  int st = __VERIFIER_nondet_int();
  int d = __VERIFIER_nondet_int();
  SIZE = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < SIZE);
  last = __VERIFIER_nondet_int();
  assume_abort_if_not(last > 0);
  a = 0;
  b = 0;
  c = 0;
  st = 0;
  d = 0;
  while (1 != 0) {
    st = 1;
    c = 0;
    while (c < SIZE) {
      if (c >= last) {
        st = 0;
      }
      c = c + 1;
    }
    if (st == 0 && c == last + 1) {
      a = a + 3;
      b = b + 3;
    } else {
      a = a + 2;
      b = b + 2;
    }
    if (c == last && st == 0) {
      a = a + 1;
    } else if (st == 1 && last < SIZE) {
      d = d + 1;
    }
    if (d == SIZE) {
      a = 0;
      b = 1;
    }
    __VERIFIER_assert(a == b && c == SIZE);
  }
  result = 0;
  return result;
}

