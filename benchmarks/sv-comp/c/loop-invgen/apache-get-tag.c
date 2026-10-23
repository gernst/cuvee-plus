// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loop-invgen/apache-get-tag.c
// SV-COMP loop-invgen/apache-get-tag.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/apache-get-tag.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "apache-get-tag.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  int tmp_4 = __VERIFIER_nondet_int();
  int tagbuf_len = __VERIFIER_nondet_int();
  int t = __VERIFIER_nondet_int();
  tagbuf_len = __VERIFIER_nondet_int();
  if (tagbuf_len >= 1) {} else {
    result = 0;
    return result;
  }
  t = 0;
  tagbuf_len = tagbuf_len - 1;
  while (1 != 0) {
    if (t == tagbuf_len) {
      __VERIFIER_assert(0 <= t);
      __VERIFIER_assert(t <= tagbuf_len);
      result = 0;
      return result;
    }
    tmp_1 = __VERIFIER_nondet_int();
    if (tmp_1 != 0) {
      break;
    }
    __VERIFIER_assert(0 <= t);
    __VERIFIER_assert(t <= tagbuf_len);
    t = t + 1;
  }
  __VERIFIER_assert(0 <= t);
  __VERIFIER_assert(t <= tagbuf_len);
  t = t + 1;
  while (1 != 0) {
    if (t == tagbuf_len) {
      __VERIFIER_assert(0 <= t);
      __VERIFIER_assert(t <= tagbuf_len);
      result = 0;
      return result;
    }
    tmp_2 = __VERIFIER_nondet_int();
    if (tmp_2 != 0) {
      tmp_3 = __VERIFIER_nondet_int();
      if (tmp_3 != 0) {
        __VERIFIER_assert(0 <= t);
        __VERIFIER_assert(t <= tagbuf_len);
        t = t + 1;
        if (t == tagbuf_len) {
          __VERIFIER_assert(0 <= t);
          __VERIFIER_assert(t <= tagbuf_len);
          result = 0;
          return result;
        }
      }
    } else {
      tmp_4 = __VERIFIER_nondet_int();
      if (tmp_4 != 0) {
        break;
      }
    }
    __VERIFIER_assert(0 <= t);
    __VERIFIER_assert(t <= tagbuf_len);
    t = t + 1;
  }
  __VERIFIER_assert(0 <= t);
  __VERIFIER_assert(t <= tagbuf_len);
  result = 0;
  return result;
}

