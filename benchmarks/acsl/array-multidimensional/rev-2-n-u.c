// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "rev-2-n-u.c", 3, "reach_error"); }

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

	int i,j;
	int m=1000,n=1500,p=1800;
	int A [m][n];
	int B [m][n];
        
        
        
	i=0;
	j=0;
	/*@ loop invariant 0 <= i <= m;
	    loop assigns i, j, B[0..m-1][0..n-1]; */
	while(i < m){
		j=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop assigns j, B[0..m-1][0..n-1]; */
		while(j < n){
					B[i][j]=__VERIFIER_nondet_int();

			j=j+1;
		}
		i=i+1;
    }


	i=0;
	j=0;
	/*@ loop invariant 0 <= i <= m;
	    loop invariant \forall integer x0, x1; 0 <= x0 < i && 0 <= x1 < n ==> A[x0][x1] == B[m-x0-1][n-x1-1];
	    loop assigns i, j, A[0..m-1][0..n-1]; */
	while(i < m){
		j=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1; 0 <= x0 < i && 0 <= x1 < n ==> A[x0][x1] == B[m-x0-1][n-x1-1];
		    loop invariant \forall integer x1; 0 <= x1 < j ==> A[i][x1] == B[m-i-1][n-x1-1];
		    loop assigns j, A[0..m-1][0..n-1]; */
		while(j < n){
			
                            A[i][j]=B[m-i-1][n-j-1];
			
			j=j+1;
		}
		i=i+1;
    }




	i=0;
	j=0;
	/*@ loop invariant 0 <= i <= m;
	    loop invariant \forall integer x0, x1; 0 <= x0 < m && 0 <= x1 < n ==> A[x0][x1] == B[m-x0-1][n-x1-1];
	    loop assigns i, j; */
	while(i < m){
		j=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1; 0 <= x0 < m && 0 <= x1 < n ==> A[x0][x1] == B[m-x0-1][n-x1-1];
		    loop assigns j; */
		while(j < n){
			
                            __VERIFIER_assert(A[i][j]==B[m-i-1][n-j-1]);
		
			j=j+1;
		}
		i=i+1;
    }
return 0;
}
