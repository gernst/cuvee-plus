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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "array_shadowinit.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
int N;
int main() {
 N=__VERIFIER_nondet_int();
 if(N>0) {
  int i,k;
  int a[N];
  i=0;
  k=0;
  /*@ loop invariant 0 <= i <= N;
      loop invariant k == i;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == t;
      loop assigns i, k, a[0..N-1]; */
  while(i < N) {
   a[k]=k;
   i=i+1;
   k=k+1;
  }
  i=0;
  /*@ loop invariant 0 <= i <= N;
      loop invariant \forall integer t; 0 <= t < N ==> a[t] == t;
      loop assigns i; */
  while(i < N) {
   __VERIFIER_assert(a[i]==i);
   i=i+1;
  }
 }
 return 0;
}
