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
void reach_error(void) {((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "benchmark20_conjunctive.c", 2, __extension__ __PRETTY_FUNCTION__); }));}
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
  int i = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  int sum = __VERIFIER_nondet_int();
  if (!(i==0 && n>=0 && n<=100 && sum==0)) return 0;
  /*@ loop invariant sum >= 0;
      loop invariant 0 <= i <= n;
      loop assigns sum, i; */
  while (i<n) {
    sum = sum + i;
    i++;
  }
  __VERIFIER_assert(sum>=0);
  return 0;
}
