// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "copy-partial-2-n-u.c", 3, "reach_error"); }
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

int main()
{

	int i,j;
	int m=1000,n=1500;
	int q=500,s=700;
	int A [m][n];
        int B [m][n];


	assume_abort_if_not(q<m);
	assume_abort_if_not(s<n);
        
        
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
	/*@ loop invariant 0 <= i <= q;
	    loop invariant \forall integer x0, x1; 0 <= x0 < i && 0 <= x1 < s ==> A[x0][x1] == B[x0][x1];
	    loop assigns i, j, A[0..m-1][0..n-1]; */
	while(i < q){
		j=0;
		/*@ loop invariant 0 <= i < q;
		    loop invariant 0 <= j <= s;
		    loop invariant \forall integer x0, x1; 0 <= x0 < i && 0 <= x1 < s ==> A[x0][x1] == B[x0][x1];
		    loop invariant \forall integer x1; 0 <= x1 < j ==> A[i][x1] == B[i][x1];
		    loop assigns j, A[0..m-1][0..n-1]; */
		while(j < s){
                    
					A[i][j]=B[i][j];

			j=j+1;
		}
		i=i+1;
    }




	i=0;
	j=0;
	/*@ loop invariant 0 <= i <= q;
	    loop invariant \forall integer x0, x1; 0 <= x0 < q && 0 <= x1 < s ==> A[x0][x1] == B[x0][x1];
	    loop assigns i, j; */
	while(i < q){
		j=0;
		/*@ loop invariant 0 <= i < q;
		    loop invariant 0 <= j <= s;
		    loop invariant \forall integer x0, x1; 0 <= x0 < q && 0 <= x1 < s ==> A[x0][x1] == B[x0][x1];
		    loop assigns j; */
		while(j < s){

                                __VERIFIER_assert(A[i][j]==B[i][j]);

                                j=j+1;
		}
		i=i+1;
    }

return 0;

}
