// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-industry-pattern/array_of_struct_ptr_monotonic.c
// SV-COMP array-industry-pattern/array_of_struct_ptr_monotonic.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_of_struct_ptr_monotonic.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int x;
  _Bool y;
  int t[];
  _Bool p1[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    x = __VERIFIER_nondet_int();
    t[i] = x;
    if (x == 10) {
      p1[i] = true;
    } else {
      y = __VERIFIER_nondet_bool();
      p1[i] = y;
    }
    i = i + 2;
  }
  i = 0;
  while (i < N) {
    if (t[i] == 10) {
      assert(p1[i]);
    }
    i = i + 2;
  }
}

