// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/nested_delay_nd.c
// SV-COMP loops-crafted-1/nested_delay_nd.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/nested_delay_nd.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int last;

int SIZE;

int main(void) {
  int result;
  int a;
  int b;
  int c;
  int st;
  int d;
  SIZE = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < SIZE);
  last = __VERIFIER_nondet_int();
  __VERIFIER_assume(last > 0);
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
    assert(a == b && c == SIZE);
  }
  result = 0;
  return result;
}

