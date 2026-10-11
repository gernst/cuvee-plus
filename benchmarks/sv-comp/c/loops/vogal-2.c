// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/vogal-2.c
// SV-COMP loops/vogal-2.yml, translated from benchmarks/sv-comp/dafny/loops/vogal-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "vogal-2.c", 7, "reach_error"); }
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

int main(void) {
  int result = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int cont = __VERIFIER_nondet_int();
  int tam_string = __VERIFIER_nondet_int();
  int n_caracter = __VERIFIER_nondet_int();
  int cont_aux = __VERIFIER_nondet_int();
  int M = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= M && 10 <= M && N <= M && 8 <= M && M <= 268435455);
  int string_entrada[M];
  int vetor_vogais[M];
  assume_abort_if_not(0 < N);
  i = 0;
  while (i < 10) {
    tmp_2 = __VERIFIER_nondet_int();
    vetor_vogais[i] = tmp_2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    string_entrada[i] = tmp_1;
    i = i + 1;
  }
  string_entrada[N - 1] = 0;
  n_caracter = 0;
  while (string_entrada[n_caracter] != 0) {
    n_caracter = n_caracter + 1;
  }
  cont = 0;
  i = 0;
  while (i < n_caracter) {
    j = 0;
    while (j < 8) {
      if (string_entrada[i] == vetor_vogais[j]) {
        cont = cont + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  cont_aux = 0;
  while (string_entrada[i] != 0) {
    j = 0;
    while (j < 10) {
      if (string_entrada[i] == vetor_vogais[j]) {
        cont_aux = cont_aux + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  __VERIFIER_assert(cont_aux == cont);
  result = 0;
  return result;
}

