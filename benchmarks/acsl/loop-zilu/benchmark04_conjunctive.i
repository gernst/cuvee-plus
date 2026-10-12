// ACSL annotations added by hand (benchmarks/acsl/README.md)

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

/*@ requires \false;
    assigns \nothing; */
void reach_error(void) {((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "benchmark04_conjunctive.c", 2, __extension__ __PRETTY_FUNCTION__); }));}
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
/*@ assigns \nothing; */
extern _Bool __VERIFIER_nondet_bool(void);
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!cond) {
    reach_error();
  }
}
int main() {
  int k = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  if (!(n>=1 && k>=n && j==0)) return 0;
  /*@ loop invariant 0 <= j <= n;
      loop invariant k >= n - j;
      loop assigns j, k; */
  while (j<=n-1) {
    j++;
    k--;
  }
  __VERIFIER_assert(k>=0);
  return 0;
}
