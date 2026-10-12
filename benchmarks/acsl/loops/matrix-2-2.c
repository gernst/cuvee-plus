// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (the maximum is not strictly below itself), the invariants state <= maior
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "matrix-2-2.c", 3, "reach_error"); }

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
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();

int main()
{
  unsigned int N_LIN=__VERIFIER_nondet_uint();
  unsigned int N_COL=__VERIFIER_nondet_uint();
  if (N_LIN >= 4000000000 / sizeof(int) || N_COL >= 4000000000 / sizeof(int)) {
    return 0;
  }
  unsigned int j,k;
  int matriz[N_COL][N_LIN], maior;
  
  maior = __VERIFIER_nondet_int();
  /*@ loop invariant 0 <= j <= N_COL;
      loop invariant \forall integer p, q; 0 <= p < j && 0 <= q < N_LIN ==> matriz[p][q] <= maior;
      loop assigns j, k, maior, matriz[0..N_COL-1][0..N_LIN-1]; */
  for(j=0;j<N_COL;j++)
    /*@ loop invariant 0 <= k <= N_LIN;
        loop invariant \forall integer p, q; 0 <= p < j && 0 <= q < N_LIN ==> matriz[p][q] <= maior;
        loop invariant \forall integer q; 0 <= q < k ==> matriz[j][q] <= maior;
        loop assigns k, maior, matriz[j][0..N_LIN-1]; */
    for(k=0;k<N_LIN;k++)
    {       
       matriz[j][k] = __VERIFIER_nondet_int();
       
       if(matriz[j][k]>maior)
          maior = matriz[j][k];                          
    }                       
    
  /*@ loop invariant 0 <= j <= N_COL;
      loop invariant \forall integer p, q; 0 <= p < N_COL && 0 <= q < N_LIN ==> matriz[p][q] <= maior;
      loop assigns j, k; */
  for(j=0;j<N_COL;j++)
    /*@ loop invariant 0 <= k <= N_LIN;
        loop invariant \forall integer p, q; 0 <= p < N_COL && 0 <= q < N_LIN ==> matriz[p][q] <= maior;
        loop assigns k; */
    for(k=0;k<N_LIN;k++)
      __VERIFIER_assert(matriz[j][k]<maior);    
}

