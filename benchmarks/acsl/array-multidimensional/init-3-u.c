// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "init-3-u.c", 3, "reach_error"); }

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
	int n=1000;
	int A [n][n][n];
	int C=__VERIFIER_nondet_int();

	i=0;
	j=0;
	k=0;
	/*@ loop invariant 0 <= i <= n;
	    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < n ==> A[x0][x1][x2] == C;
	    loop assigns i, j, k, A[0..n-1][0..n-1][0..n-1]; */
	while(i < n){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < n;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < n ==> A[x0][x1][x2] == C;
		    loop invariant \forall integer x1, x2; 0 <= x1 < j && 0 <= x2 < n ==> A[i][x1][x2] == C;
		    loop assigns j, k, A[0..n-1][0..n-1][0..n-1]; */
		while(j < n){
			k=0;
			/*@ loop invariant 0 <= i < n;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= n;
			    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < n ==> A[x0][x1][x2] == C;
			    loop invariant \forall integer x1, x2; 0 <= x1 < j && 0 <= x2 < n ==> A[i][x1][x2] == C;
			    loop invariant \forall integer x2; 0 <= x2 < k ==> A[i][j][x2] == C;
			    loop assigns k, A[0..n-1][0..n-1][0..n-1]; */
			while(k < n){
					A[i][j][k]=C;
					k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }




	i=0;
	j=0;
	k=0;
	/*@ loop invariant 0 <= i <= n;
	    loop invariant \forall integer x0, x1, x2; 0 <= x0 < n && 0 <= x1 < n && 0 <= x2 < n ==> A[x0][x1][x2] == C;
	    loop assigns i, j, k; */
	while(i < n){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < n;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1, x2; 0 <= x0 < n && 0 <= x1 < n && 0 <= x2 < n ==> A[x0][x1][x2] == C;
		    loop assigns j, k; */
		while(j < n){
			k=0;
			/*@ loop invariant 0 <= i < n;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= n;
			    loop invariant \forall integer x0, x1, x2; 0 <= x0 < n && 0 <= x1 < n && 0 <= x2 < n ==> A[x0][x1][x2] == C;
			    loop assigns k; */
			while(k < n){
					__VERIFIER_assert(A[i][j][k]==C);
					k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }
return 0;
}
