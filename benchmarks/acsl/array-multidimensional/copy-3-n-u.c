// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "copy-3-n-u.c", 3, "reach_error"); }

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

	int i,j,k;
	int m=1000,n=1500,p=1800;
	int A [m][n][p];
	int B [m][n][p];


	i=0;
	j=0;
	k=0;
	/*@ loop invariant 0 <= i <= m;
	    loop assigns i, j, k, B[0..m-1][0..n-1][0..p-1]; */
	while(i < m){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop assigns j, k, B[0..m-1][0..n-1][0..p-1]; */
		while(j < n){
			k=0;
			/*@ loop invariant 0 <= i < m;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= p;
			    loop assigns k, B[0..m-1][0..n-1][0..p-1]; */
			while(k < p){
					B[i][j][k]=__VERIFIER_nondet_int();
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
	    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
	    loop assigns i, j, k, A[0..m-1][0..n-1][0..p-1]; */
	while(i < m){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
		    loop invariant \forall integer x1, x2; 0 <= x1 < j && 0 <= x2 < p ==> A[i][x1][x2] == B[i][x1][x2];
		    loop assigns j, k, A[0..m-1][0..n-1][0..p-1]; */
		while(j < n){
			k=0;
			/*@ loop invariant 0 <= i < m;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= p;
			    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
			    loop invariant \forall integer x1, x2; 0 <= x1 < j && 0 <= x2 < p ==> A[i][x1][x2] == B[i][x1][x2];
			    loop invariant \forall integer x2; 0 <= x2 < k ==> A[i][j][x2] == B[i][j][x2];
			    loop assigns k, A[0..m-1][0..n-1][0..p-1]; */
			while(k < p){
					A[i][j][k]=B[i][j][k];
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
	    loop invariant \forall integer x0, x1, x2; 0 <= x0 < m && 0 <= x1 < n && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
	    loop assigns i, j, k; */
	while(i < m){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1, x2; 0 <= x0 < m && 0 <= x1 < n && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
		    loop assigns j, k; */
		while(j < n){
			k=0;
			/*@ loop invariant 0 <= i < m;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= p;
			    loop invariant \forall integer x0, x1, x2; 0 <= x0 < m && 0 <= x1 < n && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
			    loop assigns k; */
			while(k < p){
					__VERIFIER_assert(A[i][j][k]==B[i][j][k]);
					k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }
return 0;
}
