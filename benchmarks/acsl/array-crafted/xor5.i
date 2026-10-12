// ACSL annotations added by hand (benchmarks/acsl/README.md): the result of xor is the logic function fold of the axiomatic Fold, invariant under the swap and the rotation by the lemmas fold_swap and fold_rotate (labels L1, L2)


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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "xor5.c", 5, __extension__ __PRETTY_FUNCTION__); })); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);

int N;

/*@ axiomatic Fold {
  logic integer fold(int *x, integer n) reads x[0..n-1];
  axiom fold_base: \forall int *x; fold(x, 1) == x[0];
  axiom fold_step: \forall int *x, integer n; n >= 1 ==> fold(x, n+1) == fold(x, n) ^ x[n];
  lemma fold_swap{L1, L2}: \forall int *x, integer n; n >= 2 && \at(x[0], L2) == \at(x[1], L1) && \at(x[1], L2) == \at(x[0], L1)
    && (\forall integer k; 2 <= k < n ==> \at(x[k], L2) == \at(x[k], L1)) ==> \at(fold(x, n), L2) == \at(fold(x, n), L1);
  lemma fold_rotate{L1, L2}: \forall int *x, integer n; n >= 1 && (\forall integer k; 0 <= k < n-1 ==> \at(x[k], L2) == \at(x[k+1], L1))
    && \at(x[n-1], L2) == \at(x[0], L1) ==> \at(fold(x, n), L2) == \at(fold(x, n), L1);
} */
/*@ requires N >= 1;
    requires \valid_read(x + (0..N-1));
    assigns \nothing;
    ensures \result == (int) fold(x, N); */
int xor (int x[N])
{
  int i;
  long long res;
  res = x[0];
  /*@ loop invariant 1 <= i <= N;
      loop invariant res == fold(x, i);
      loop assigns i, res; */
  for (i = 1; i < N; i++) {
    res = res ^ x[i];
  }
  return res;
}

int main ()
{
  N = __VERIFIER_nondet_int();
  if (N > 1) {
    int x[N];
    int temp;
    int ret;
    int ret2;
    int ret5;
		
		/*@ loop invariant 0 <= i <= N;
		    loop assigns i, x[0..N-1]; */
		for(int i = 0; i < N; i++) 
		{
		  x[i] = __VERIFIER_nondet_int();
		}

    L1: ;
    ret = xor(x);

    temp=x[0];x[0] = x[1]; x[1] = temp;
    //@ assert fold(x, N) == \at(fold(x, N), L1);
    L2: ;
    ret2 = xor(x);
    temp=x[0];
    /*@ loop invariant 0 <= i <= N-1;
        loop invariant \forall integer k; 0 <= k < i ==> x[k] == \at(x[k+1], L2);
        loop invariant \forall integer k; i <= k < N ==> x[k] == \at(x[k], L2);
        loop invariant temp == \at(x[0], L2);
        loop assigns i, x[0..N-2]; */
    for(int i =0 ; i<N-1; i++){
       x[i] = x[i+1];
    }
    x[N-1] = temp;
    //@ assert fold(x, N) == \at(fold(x, N), L2);
    ret5 = xor(x);

    if(ret != ret2 || ret !=ret5){
      {reach_error();}
    }
  }
  return 1;
}
