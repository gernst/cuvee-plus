// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/single_elem_safe.c
// SV-COMP array-lopstr16/single_elem_safe.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/single_elem_safe.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int q;
  int v;
  _Bool w;
  _Bool s[];
  int n[];
  _Bool p[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    q = __VERIFIER_nondet_int();
    if (q == 0) {
      s[i] = true;
      n[i] = q % 2;
      if (n[i] == 0) {
        p[i] = true;
      } else {
        p[i] = false;
      }
    } else {
      s[i] = false;
    }
    i = i + 1;
  }
  v = __VERIFIER_nondet_int();
  w = __VERIFIER_nondet_bool();
  s[3] = true;
  n[3] = v;
  p[3] = w;
  i = 0;
  while (i < N) {
    if (i != 3 && s[i] && n[i] == 0) {
      assert(p[i]);
    }
    i = i + 1;
  }
}

