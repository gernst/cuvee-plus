// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (A[1023] == 1023 after the loop)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array_1-1.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main(void) {
  int A[2048];
  int i;

  /*@ loop invariant 0 <= i <= 1024;
      loop invariant \forall integer t; 0 <= t < i ==> A[t] == t;
      loop assigns i, A[0..1023]; */
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }

  __VERIFIER_assert(A[1023] != 1023);
}
