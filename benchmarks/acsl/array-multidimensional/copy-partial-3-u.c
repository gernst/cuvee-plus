// ACSL annotations added by hand (benchmarks/acsl/README.md): the two copies cover the cells below p and the cells at or above p in all coordinates; the assertion on the other cells is not implied by these invariants
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "copy-partial-3-u.c", 3, "reach_error"); }
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

	int i,j,k;
	int n=1000;
	int p=500;
	int A [n][n][n];
        int B [n][n][n];
	assume_abort_if_not(p<n);
        

	i=0;
	j=0;
	k=0;

	/*@ loop invariant 0 <= i <= n;
	    loop assigns i, j, k, B[0..n-1][0..n-1][0..n-1]; */
	while(i < n){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < n;
		    loop invariant 0 <= j <= n;
		    loop assigns j, k, B[0..n-1][0..n-1][0..n-1]; */
		while(j < n){
			k=0;
			/*@ loop invariant 0 <= i < n;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= n;
			    loop assigns k, B[0..n-1][0..n-1][0..n-1]; */
			while(k < n){
					B[i][j][k] = __VERIFIER_nondet_int();
					k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }




	i=0;
	j=0;
	k=0;

	/*@ loop invariant 0 <= i <= p;
	    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < p && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
	    loop assigns i, j, k, A[0..n-1][0..n-1][0..n-1]; */
	while(i < p){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < p;
		    loop invariant 0 <= j <= p;
		    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < p && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
		    loop invariant \forall integer x1, x2; 0 <= x1 < j && 0 <= x2 < p ==> A[i][x1][x2] == B[i][x1][x2];
		    loop assigns j, k, A[0..n-1][0..n-1][0..n-1]; */
		while(j < p){
			k=0;
			/*@ loop invariant 0 <= i < p;
			    loop invariant 0 <= j < p;
			    loop invariant 0 <= k <= p;
			    loop invariant \forall integer x0, x1, x2; 0 <= x0 < i && 0 <= x1 < p && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
			    loop invariant \forall integer x1, x2; 0 <= x1 < j && 0 <= x2 < p ==> A[i][x1][x2] == B[i][x1][x2];
			    loop invariant \forall integer x2; 0 <= x2 < k ==> A[i][j][x2] == B[i][j][x2];
			    loop assigns k, A[0..n-1][0..n-1][0..n-1]; */
			while(k < p){
					A[i][j][k]=B[i][j][k];
					k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }
		
		i=p;
		/*@ loop invariant p <= i <= n;
		    loop invariant \forall integer x0, x1, x2; 0 <= x0 < p && 0 <= x1 < p && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
		    loop invariant \forall integer x0, x1, x2; p <= x0 < i && p <= x1 < n && p <= x2 < n ==> A[x0][x1][x2] == B[x0][x1][x2];
		    loop assigns i, j, k, A[0..n-1][0..n-1][0..n-1]; */
		while(i < n){
		j=p;
		/*@ loop invariant p <= i < n;
		    loop invariant p <= j <= n;
		    loop invariant \forall integer x0, x1, x2; 0 <= x0 < p && 0 <= x1 < p && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
		    loop invariant \forall integer x0, x1, x2; p <= x0 < i && p <= x1 < n && p <= x2 < n ==> A[x0][x1][x2] == B[x0][x1][x2];
		    loop invariant \forall integer x1, x2; p <= x1 < j && p <= x2 < n ==> A[i][x1][x2] == B[i][x1][x2];
		    loop assigns j, k, A[0..n-1][0..n-1][0..n-1]; */
		while(j < n){
			k=p;
			/*@ loop invariant p <= i < n;
			    loop invariant p <= j < n;
			    loop invariant p <= k <= n;
			    loop invariant \forall integer x0, x1, x2; 0 <= x0 < p && 0 <= x1 < p && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
			    loop invariant \forall integer x0, x1, x2; p <= x0 < i && p <= x1 < n && p <= x2 < n ==> A[x0][x1][x2] == B[x0][x1][x2];
			    loop invariant \forall integer x1, x2; p <= x1 < j && p <= x2 < n ==> A[i][x1][x2] == B[i][x1][x2];
			    loop invariant \forall integer x2; p <= x2 < k ==> A[i][j][x2] == B[i][j][x2];
			    loop assigns k, A[0..n-1][0..n-1][0..n-1]; */
			while(k < n){
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
	/*@ loop invariant 0 <= i <= n;
	    loop invariant \forall integer x0, x1, x2; 0 <= x0 < p && 0 <= x1 < p && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
	    loop invariant \forall integer x0, x1, x2; p <= x0 < n && p <= x1 < n && p <= x2 < n ==> A[x0][x1][x2] == B[x0][x1][x2];
	    loop assigns i, j, k; */
	while(i < n){
		j=0;
		k=0;
		/*@ loop invariant 0 <= i < n;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1, x2; 0 <= x0 < p && 0 <= x1 < p && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
		    loop invariant \forall integer x0, x1, x2; p <= x0 < n && p <= x1 < n && p <= x2 < n ==> A[x0][x1][x2] == B[x0][x1][x2];
		    loop assigns j, k; */
		while(j < n){
			k=0;
			/*@ loop invariant 0 <= i < n;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= n;
			    loop invariant \forall integer x0, x1, x2; 0 <= x0 < p && 0 <= x1 < p && 0 <= x2 < p ==> A[x0][x1][x2] == B[x0][x1][x2];
			    loop invariant \forall integer x0, x1, x2; p <= x0 < n && p <= x1 < n && p <= x2 < n ==> A[x0][x1][x2] == B[x0][x1][x2];
			    loop assigns k; */
			while(k < n){
					__VERIFIER_assert(A[i][j][k]==B[i][j][k]);
					k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }
return 0;
}
