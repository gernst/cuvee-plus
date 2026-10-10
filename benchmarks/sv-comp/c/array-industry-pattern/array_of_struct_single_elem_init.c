// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-industry-pattern/array_of_struct_single_elem_init.c
// SV-COMP array-industry-pattern/array_of_struct_single_elem_init.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_of_struct_single_elem_init.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int i;
  int q;
  int x;
  int n[];
  int p[];
  __VERIFIER_assume(0 < N);
  i = 0;
  while (i < N) {
    q = __VERIFIER_nondet_int();
    x = __VERIFIER_nondet_int();
    if (x == 0) {
      p[i] = 10;
    } else {
      p[i] = 20;
    }
    n[i] = x;
    i = i + 1;
  }
  p[3] = 30;
  n[3] = 40;
  i = 0;
  while (i < N) {
    if (i != 3 && n[i] == 0) {
      assert(p[i] == 10);
    }
    i = i + 1;
  }
}

