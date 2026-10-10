// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/watermelon.c
// SV-COMP loops-crafted-1/watermelon.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/watermelon.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int true;

int false;

int correct_version(int w) {
  int result;
  int is_divisible;
  int i;
  is_divisible = true;
  if (w < 4) {
    is_divisible = false;
  } else {
    i = 0;
    while (i < w) {
      i = i + 2;
    }
    if (i != w) {
      is_divisible = false;
    }
  }
  result = is_divisible;
  return result;
}

int student_version(int w) {
  int result;
  int is_divisible;
  int i;
  is_divisible = true;
  if (w < 4) {
    is_divisible = false;
  } else {
    i = 0;
    while (i < w) {
      i = i + 2;
    }
    if (i != w) {
      is_divisible = false;
    }
  }
  result = is_divisible;
  return result;
}

int main(void) {
  int result;
  int tmp_1;
  int w;
  int is_divisible1;
  int is_divisible2;
  true = 1;
  false = 0;
  tmp_1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= tmp_1);
  w = tmp_1;
  is_divisible1 = true;
  is_divisible2 = true;
  if (w > 0) {
    is_divisible1 = correct_version(w);
    is_divisible2 = student_version(w);
    assert(is_divisible1 == is_divisible2);
  }
  result = 0;
  return result;
}

