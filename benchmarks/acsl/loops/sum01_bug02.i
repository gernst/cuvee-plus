// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (sn stops growing when i >= j)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);

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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "sum01_bug02.c", 3, __extension__ __PRETTY_FUNCTION__); })); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint();
int main() {
  int i, j=10, n=__VERIFIER_nondet_uint(), sn=0;
  if (n==2147483647) {
    return 0;
  }
  /*@ loop invariant 1 <= i && (i <= n+1 || i == 1);
      loop invariant j == 11 - i;
      loop invariant 0 <= sn <= 2*(i-1);
      loop assigns i, j, sn; */
  for(i=1; i<=n; i++) {
    if (i<j)
    sn = sn + (2);
    j--;
  }
  __VERIFIER_assert(sn==((long long) n)*(2) || sn == 0);
}
