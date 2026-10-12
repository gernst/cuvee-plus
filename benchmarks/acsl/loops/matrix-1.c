// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "matrix-1.c", 3, "reach_error"); }

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
  unsigned int N_LIN=1;
  unsigned int N_COL=1;      
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
       
       if(matriz[j][k]>=maior)
          maior = matriz[j][k];                          
    }                       
    
  __VERIFIER_assert(matriz[0][0]<=maior);    

  return 0;
}

