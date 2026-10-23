// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops/vogal-1.c
// SV-COMP loops/vogal-1.yml, translated from benchmarks/sv-comp/dafny/loops/vogal-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "vogal-1.c", 7, "reach_error"); }
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
  assume_abort_if_not(0 <= N && N <= 268435455);
  assume_abort_if_not(0 < N);
  int input_string[N], vogal_array[N];
  i = 0;
  while (i < N / 2) {
    tmp_2 = __VERIFIER_nondet_int();
    vogal_array[i] = tmp_2;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    input_string[i] = tmp_1;
    i = i + 1;
  }
  if (input_string[N - 1] != 0) {
    result = 0;
    return result;
  }
  n_caracter = 0;
  while (input_string[n_caracter] != 0) {
    n_caracter = n_caracter + 1;
  }
  cont = 0;
  i = 0;
  while (i < n_caracter) {
    j = 0;
    while (j < N / 2) {
      if (input_string[i] == vogal_array[j]) {
        cont = cont + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  cont_aux = 0;
  while (input_string[i] != 0) {
    j = 0;
    while (j < N / 2) {
      if (input_string[i] == vogal_array[j]) {
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

