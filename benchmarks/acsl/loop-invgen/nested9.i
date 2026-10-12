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
int __BLAST_NONDET;
int main() {
    int i,j,k,n,l,m;
    n = __VERIFIER_nondet_int();
    m = __VERIFIER_nondet_int();
    l = __VERIFIER_nondet_int();
    if (!(-1000000 < n && n < 1000000)) return 0;
    if (!(-1000000 < m && m < 1000000)) return 0;
    if (!(-1000000 < l && l < 1000000)) return 0;
    if(3*n<=m+l); else goto END;
    /*@ loop invariant 0 <= i;
        loop invariant i <= n || i == 0;
        loop assigns i, j, k; */
    for (i=0;i<n;i++)
        /*@ loop invariant 0 <= i < n;
            loop invariant 2*i <= j <= 3*i;
            loop assigns j, k; */
        for (j = 2*i;j<3*i;j++)
            /*@ loop invariant 0 <= i < n;
                loop invariant j < 3*i;
                loop invariant i <= k <= j;
                loop assigns k; */
            for (k = i; k< j; k++)
                __VERIFIER_assert( k-i <= 2*n );
END:
    return 0;
}
