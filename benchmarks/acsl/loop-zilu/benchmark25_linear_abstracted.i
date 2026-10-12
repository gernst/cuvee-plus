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
void reach_error(void) {((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "benchmark25_linear_abstracted.c", 2, __extension__ __PRETTY_FUNCTION__); }));}
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
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
  int x = __VERIFIER_nondet_int();
  if (!(x<0)) return 0;
  if (x < (10)) {
  x = __VERIFIER_nondet_int();
  if (!(x < (10))) abort();
  if (x<10) {
      x=x+1;
    }
  if (x < (10)) abort();
  }
  __VERIFIER_assert(x==10);
  return 0;
}
