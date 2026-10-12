// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (sn stops growing at x == 10)
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "sum03-1.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
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
  int sn=0;
  unsigned int loop1=__VERIFIER_nondet_uint(), n1=__VERIFIER_nondet_uint();
  unsigned int x=0;
  /*@ loop invariant x <= 10 ==> sn == 2*x;
      loop invariant x > 10 ==> sn == 20;
      loop assigns sn, x; */
  while(1){
      if (x<10) {
          sn = sn + (2);
      }
      x++;
      __VERIFIER_assert(sn==x*(2) || sn == 0);
  }
}
