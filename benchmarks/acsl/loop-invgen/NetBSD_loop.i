// ACSL annotations added by hand (benchmarks/acsl/README.md)
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "assert.h", 3, __extension__ __PRETTY_FUNCTION__); })); }
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();
int main ()
{
  int MAXPATHLEN;
  int pathbuf_off;
  int bound_off;
  int glob2_p_off;
  int glob2_pathbuf_off;
  int glob2_pathlim_off;
  MAXPATHLEN = __VERIFIER_nondet_int();
  if(MAXPATHLEN > 0 && MAXPATHLEN < 2147483647); else goto END;
  pathbuf_off = 0;
  bound_off = pathbuf_off + (MAXPATHLEN + 1) - 1;
  glob2_pathbuf_off = pathbuf_off;
  glob2_pathlim_off = bound_off;
  /*@ loop invariant 0 <= glob2_p_off;
      loop invariant glob2_p_off <= glob2_pathlim_off + 1;
      loop invariant glob2_pathlim_off == MAXPATHLEN;
      loop assigns glob2_p_off; */
  for (glob2_p_off = glob2_pathbuf_off;
      glob2_p_off <= glob2_pathlim_off;
      glob2_p_off++) {
    __VERIFIER_assert (0 <= glob2_p_off );
    __VERIFIER_assert (glob2_p_off < MAXPATHLEN + 1);
  }
 END: return 0;
}
