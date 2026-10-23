// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops-crafted-1/watermelon.c
// SV-COMP loops-crafted-1/watermelon.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/watermelon.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "watermelon.c", 7, "reach_error"); }
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



int correct_version(int w) {
  int result = __VERIFIER_nondet_int();
  int is_divisible = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  is_divisible = 1;
  if (w < 4) {
    is_divisible = 0;
  } else {
    i = 0;
    while (i < w) {
      i = i + 2;
    }
    if (i != w) {
      is_divisible = 0;
    }
  }
  result = is_divisible;
  return result;
}

int student_version(int w) {
  int result = __VERIFIER_nondet_int();
  int is_divisible = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  is_divisible = 1;
  if (w < 4) {
    is_divisible = 0;
  } else {
    i = 0;
    while (i < w) {
      i = i + 2;
    }
    if (i != w) {
      is_divisible = 0;
    }
  }
  result = is_divisible;
  return result;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int w = __VERIFIER_nondet_int();
  int is_divisible1 = __VERIFIER_nondet_int();
  int is_divisible2 = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  w = tmp_1;
  is_divisible1 = 1;
  is_divisible2 = 1;
  if (w > 0) {
    is_divisible1 = correct_version(w);
    is_divisible2 = student_version(w);
    __VERIFIER_assert(is_divisible1 == is_divisible2);
  }
  result = 0;
  return result;
}

