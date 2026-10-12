// ACSL annotations added by hand (benchmarks/acsl/README.md): the elements are unsigned, the sum is stated modulo 2^32
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "add-2-n-u.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
unsigned int __VERIFIER_nondet_uint();

int main()
{

	int i,j;
	int m=1000,n=1500;
	unsigned int A [m][n];
        unsigned int B [m][n];
        unsigned int C [m][n];

	i=0;
	j=0;
	/*@ loop invariant 0 <= i <= m;
	    loop assigns i, j, A[0..m-1][0..n-1], B[0..m-1][0..n-1]; */
	while(i < m){
		j=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop assigns j, A[0..m-1][0..n-1], B[0..m-1][0..n-1]; */
		while(j < n){
					A[i][j]=__VERIFIER_nondet_uint();
					B[i][j]=__VERIFIER_nondet_uint();

			j=j+1;
		}
		i=i+1;
    }
	

	i=0;
	j=0;
	/*@ loop invariant 0 <= i <= m;
	    loop invariant \forall integer x0, x1; 0 <= x0 < i && 0 <= x1 < n ==> (C[x0][x1] - (A[x0][x1] + B[x0][x1])) % 4294967296 == 0;
	    loop assigns i, j, C[0..m-1][0..n-1]; */
	while(i < m){
		j=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1; 0 <= x0 < i && 0 <= x1 < n ==> (C[x0][x1] - (A[x0][x1] + B[x0][x1])) % 4294967296 == 0;
		    loop invariant \forall integer x1; 0 <= x1 < j ==> (C[i][x1] - (A[i][x1] + B[i][x1])) % 4294967296 == 0;
		    loop assigns j, C[0..m-1][0..n-1]; */
		while(j < n){
					C[i][j]=A[i][j]+B[i][j];

			j=j+1;
		}
		i=i+1;
    }



	i=0;
	j=0;
	/*@ loop invariant 0 <= i <= m;
	    loop invariant \forall integer x0, x1; 0 <= x0 < m && 0 <= x1 < n ==> (C[x0][x1] - (A[x0][x1] + B[x0][x1])) % 4294967296 == 0;
	    loop assigns i, j; */
	while(i < m){
		j=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1; 0 <= x0 < m && 0 <= x1 < n ==> (C[x0][x1] - (A[x0][x1] + B[x0][x1])) % 4294967296 == 0;
		    loop assigns j; */
		while(j < n){
					__VERIFIER_assert(C[i][j]==A[i][j]+B[i][j]);

			j=j+1;
		}
		i=i+1;
    }


return 0;

}
