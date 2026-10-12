// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "transpose-u.c", 3, "reach_error"); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();
int main()
{

	int i;
	int k;
	int j;
	int n=1000;
        int m=1800;
	int A[n][n];
	int C[n][n];

	/*@ loop invariant 0 <= i <= n;
	    loop assigns i, j, A[0..n-1][0..n-1]; */
	for ( i = 0 ; i < n ; i++ ){
          /*@ loop invariant 0 <= i < n;
              loop invariant 0 <= j <= n;
              loop assigns j, A[0..n-1][0..n-1]; */
          for ( j = 0 ; j < n ; j++ ){
                A[i][j]= __VERIFIER_nondet_int();
          }
    }


	i=0;
	j=0;

	/*@ loop invariant 0 <= i <= n;
	    loop invariant \forall integer x0, x1; 0 <= x0 < i && 0 <= x1 < n ==> C[x1][x0] == A[x0][x1];
	    loop assigns i, j, C[0..n-1][0..n-1]; */
	while(i < n){
		  j=0;
           /*@ loop invariant 0 <= i < n;
               loop invariant 0 <= j <= n;
               loop invariant \forall integer x0, x1; 0 <= x0 < i && 0 <= x1 < n ==> C[x1][x0] == A[x0][x1];
               loop invariant \forall integer x1; 0 <= x1 < j ==> C[x1][i] == A[i][x1];
               loop assigns j, C[0..n-1][0..n-1]; */
           while(j < n){
                C[j][i] = A[i][j];
		  		j=j+1;
          }
	i=i+1;
    }

	/*@ loop invariant 0 <= i <= n;
	    loop invariant \forall integer x0, x1; 0 <= x0 < n && 0 <= x1 < n ==> C[x1][x0] == A[x0][x1];
	    loop assigns i, j; */
	for ( i = 0 ; i < n ; i++ ){
          /*@ loop invariant 0 <= i < n;
              loop invariant 0 <= j <= n;
              loop invariant \forall integer x0, x1; 0 <= x0 < n && 0 <= x1 < n ==> C[x1][x0] == A[x0][x1];
              loop assigns j; */
          for ( j = 0 ; j < n ; j++ ){
                __VERIFIER_assert(C[j][i] == A[i][j]);
          }
    }
return 0;
}
