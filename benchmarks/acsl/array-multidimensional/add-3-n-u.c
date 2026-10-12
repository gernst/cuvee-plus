// ACSL annotations added by hand (benchmarks/acsl/README.md): the elements are unsigned, the sum is stated modulo 2^32
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "add-3-n-u.c", 3, "reach_error"); }

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

	int i,j,k;
	int m=1000,n=1500,p=1800;
	unsigned int A [m][n][p];
        unsigned int B [m][n][p];
        unsigned int C [m][n][p];
	
	i=0;
	j=0;
	k=0;
	/*@ loop invariant 0 <= i <= m;
	    loop assigns i, j, k, A[0..m-1][0..n-1][0..p-1], B[0..m-1][0..n-1][0..p-1]; */
	while(i < m){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop assigns j, k, A[0..m-1][0..n-1][0..p-1], B[0..m-1][0..n-1][0..p-1]; */
		while(j < n){
			k=0;
			/*@ loop invariant 0 <= i < m;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= p;
			    loop assigns k, A[0..m-1][0..n-1][0..p-1], B[0..m-1][0..n-1][0..p-1]; */
			while(k < p){
					A[i][j][k]= __VERIFIER_nondet_uint();
                                        B[i][j][k]= __VERIFIER_nondet_uint();
					k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }

	i=0;
	j=0;
	k=0;
	/*@ loop invariant 0 <= i <= m;
	    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < p ==> (C[x0][x1][x2] - (A[x0][x1][x2] + B[x0][x1][x2])) % 4294967296 == 0;
	    loop assigns i, j, k, C[0..m-1][0..n-1][0..p-1]; */
	while(i < m){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < p ==> (C[x0][x1][x2] - (A[x0][x1][x2] + B[x0][x1][x2])) % 4294967296 == 0;
		    loop invariant \forall integer x1, x2; 0 <= x1 < j && 0 <= x2 < p ==> (C[i][x1][x2] - (A[i][x1][x2] + B[i][x1][x2])) % 4294967296 == 0;
		    loop assigns j, k, C[0..m-1][0..n-1][0..p-1]; */
		while(j < n){
			k=0;
			/*@ loop invariant 0 <= i < m;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= p;
			    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < p ==> (C[x0][x1][x2] - (A[x0][x1][x2] + B[x0][x1][x2])) % 4294967296 == 0;
			    loop invariant \forall integer x1, x2; 0 <= x1 < j && 0 <= x2 < p ==> (C[i][x1][x2] - (A[i][x1][x2] + B[i][x1][x2])) % 4294967296 == 0;
			    loop invariant \forall integer x2; 0 <= x2 < k ==> (C[i][j][x2] - (A[i][j][x2] + B[i][j][x2])) % 4294967296 == 0;
			    loop assigns k, C[0..m-1][0..n-1][0..p-1]; */
			while(k < p){
					C[i][j][k]=A[i][j][k]+B[i][j][k];
					k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }




	i=0;
	j=0;
	k=0;
	/*@ loop invariant 0 <= i <= m;
	    loop invariant \forall integer x0, x1, x2; 0 <= x0 < m && 0 <= x1 < n && 0 <= x2 < p ==> (C[x0][x1][x2] - (A[x0][x1][x2] + B[x0][x1][x2])) % 4294967296 == 0;
	    loop assigns i, j, k; */
	while(i < m){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1, x2; 0 <= x0 < m && 0 <= x1 < n && 0 <= x2 < p ==> (C[x0][x1][x2] - (A[x0][x1][x2] + B[x0][x1][x2])) % 4294967296 == 0;
		    loop assigns j, k; */
		while(j < n){
			k=0;
			/*@ loop invariant 0 <= i < m;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= p;
			    loop invariant \forall integer x0, x1, x2; 0 <= x0 < m && 0 <= x1 < n && 0 <= x2 < p ==> (C[x0][x1][x2] - (A[x0][x1][x2] + B[x0][x1][x2])) % 4294967296 == 0;
			    loop assigns k; */
			while(k < p){
					__VERIFIER_assert(C[i][j][k]==A[i][j][k]+B[i][j][k]);
					k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }
return 0;
}
