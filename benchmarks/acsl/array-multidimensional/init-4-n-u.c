// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "init-4-n-u.c", 3, "reach_error"); }

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

	int i,j,k,l;
	int m=1000,n=1500,p=1800,q=2000;
	int A [m][n][p][q];
	int C=__VERIFIER_nondet_int();
        
        

	i=0;
	j=0;
	k=0;
        l=0;
	/*@ loop invariant 0 <= i <= m;
	    loop invariant \forall integer x0, x1, x2, x3; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < p && 0 <= x3 < q ==> A[x0][x1][x2][x3] == C;
	    loop assigns i, j, k, l, A[0..m-1][0..n-1][0..p-1][0..q-1]; */
	while(i < m){
		j=0;
		k=0;
                l=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1, x2, x3; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < p && 0 <= x3 < q ==> A[x0][x1][x2][x3] == C;
		    loop invariant \forall integer x1, x2, x3; 0 <= x1 < j && 0 <= x2 < p && 0 <= x3 < q ==> A[i][x1][x2][x3] == C;
		    loop assigns j, k, l, A[0..m-1][0..n-1][0..p-1][0..q-1]; */
		while(j < n){
			k=0;
                        l=0;
			/*@ loop invariant 0 <= i < m;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= p;
			    loop invariant \forall integer x0, x1, x2, x3; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < p && 0 <= x3 < q ==> A[x0][x1][x2][x3] == C;
			    loop invariant \forall integer x1, x2, x3; 0 <= x1 < j && 0 <= x2 < p && 0 <= x3 < q ==> A[i][x1][x2][x3] == C;
			    loop invariant \forall integer x2, x3; 0 <= x2 < k && 0 <= x3 < q ==> A[i][j][x2][x3] == C;
			    loop assigns k, l, A[0..m-1][0..n-1][0..p-1][0..q-1]; */
			while(k < p){
                            l=0;
                            /*@ loop invariant 0 <= i < m;
                                loop invariant 0 <= j < n;
                                loop invariant 0 <= k < p;
                                loop invariant 0 <= l <= q;
                                loop invariant \forall integer x0, x1, x2, x3; 0 <= x0 < i && 0 <= x1 < n && 0 <= x2 < p && 0 <= x3 < q ==> A[x0][x1][x2][x3] == C;
                                loop invariant \forall integer x1, x2, x3; 0 <= x1 < j && 0 <= x2 < p && 0 <= x3 < q ==> A[i][x1][x2][x3] == C;
                                loop invariant \forall integer x2, x3; 0 <= x2 < k && 0 <= x3 < q ==> A[i][j][x2][x3] == C;
                                loop invariant \forall integer x3; 0 <= x3 < l ==> A[i][j][k][x3] == C;
                                loop assigns l, A[0..m-1][0..n-1][0..p-1][0..q-1]; */
                            while(l < q){
					A[i][j][k][l]=C;
                                        l=l+1;
                                        }
                        k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }


	i=0;
	j=0;
	k=0;
        l=0;
	/*@ loop invariant 0 <= i <= m;
	    loop invariant \forall integer x0, x1, x2, x3; 0 <= x0 < m && 0 <= x1 < n && 0 <= x2 < p && 0 <= x3 < q ==> A[x0][x1][x2][x3] == C;
	    loop assigns i, j, k, l; */
	while(i < m){
		j=0;
		k=0;
                l=0;
		/*@ loop invariant 0 <= i < m;
		    loop invariant 0 <= j <= n;
		    loop invariant \forall integer x0, x1, x2, x3; 0 <= x0 < m && 0 <= x1 < n && 0 <= x2 < p && 0 <= x3 < q ==> A[x0][x1][x2][x3] == C;
		    loop assigns j, k, l; */
		while(j < n){
			k=0;
                        l=0;
			/*@ loop invariant 0 <= i < m;
			    loop invariant 0 <= j < n;
			    loop invariant 0 <= k <= p;
			    loop invariant \forall integer x0, x1, x2, x3; 0 <= x0 < m && 0 <= x1 < n && 0 <= x2 < p && 0 <= x3 < q ==> A[x0][x1][x2][x3] == C;
			    loop assigns k, l; */
			while(k < p){
                            l=0;
                            /*@ loop invariant 0 <= i < m;
                                loop invariant 0 <= j < n;
                                loop invariant 0 <= k < p;
                                loop invariant 0 <= l <= q;
                                loop invariant \forall integer x0, x1, x2, x3; 0 <= x0 < m && 0 <= x1 < n && 0 <= x2 < p && 0 <= x3 < q ==> A[x0][x1][x2][x3] == C;
                                loop assigns l; */
                            while(l < q){
					__VERIFIER_assert(A[i][j][k][l]==C);
					l=l+1;
                                }
                                k=k+1;
			}
			j=j+1;
		}
		i=i+1;
    }


return 0;
}
