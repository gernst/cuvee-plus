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
int main()
{
  int p;
  int i;
  int leader_len;
  int bufsize;
  int bufsize_0;
  int ielen;
  leader_len = __VERIFIER_nondet_int();
  bufsize = __VERIFIER_nondet_int();
  ielen = __VERIFIER_nondet_int();
  if (!(leader_len < 1000000)) return 0;
  if (!(bufsize < 1000000)) return 0;
  if (!(ielen < 1000000)) return 0;
  if(leader_len >0); else goto END;
  if(bufsize >0); else goto END;
  if(ielen >0); else goto END;
  if (bufsize < leader_len)
    goto END;
  p = 0;
  bufsize_0 = bufsize;
  bufsize -= leader_len;
  p += leader_len;
  if (bufsize < 2*ielen)
    goto END;
  /*@ loop invariant 0 <= i <= ielen;
      loop invariant p == leader_len + 2*i;
      loop invariant bufsize + leader_len == bufsize_0;
      loop invariant bufsize >= 2*ielen;
      loop invariant leader_len > 0;
      loop assigns i, p; */
  for (i = 0; i < ielen && bufsize > 2; i++) {
    __VERIFIER_assert(0<=p);
    __VERIFIER_assert(p+1<bufsize_0);
    p += 2;
  }
 END:
  ;
}
