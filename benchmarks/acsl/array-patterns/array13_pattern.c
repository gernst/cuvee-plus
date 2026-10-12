// ACSL annotations added by hand (benchmarks/acsl/README.md): the sums are the logic functions of the axiomatic Msum over the flattened matrix, the final bound follows from the element-wise property by the lemma total
/*


   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

/* Program Description :-
 * A square 2D array is declared.
 * All elements are initialized with 0.
 * In while(1) loop,  two indices are selected non-deterministically.
 * Array[index1][index2] is initialized with num^4, if it belongs to lower
 * triangular matrix, below main diagonal.
 * Sum of array should never exceed lower triangular matrix entries summation. 
 * */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array13_pattern.c", 28, "reach_error"); }
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int() ;
/*@ assigns \nothing; */
extern short __VERIFIER_nondet_short() ;

signed long long ARR_SIZE ;

/*@ axiomatic Msum {
  logic integer rsum(int *r, integer n) reads r[0..n-1];
  axiom rsum_zero: \forall int *r; rsum(r, 0) == 0;
  axiom rsum_step: \forall int *r, integer n; n >= 0 ==> rsum(r, n+1) == rsum(r, n) + r[n];
  // the sum of the first rows of a matrix with n columns, flattened
  logic integer msum(int *a, integer n, integer rows) reads a[0..n*rows-1];
  axiom msum_zero: \forall int *a, integer n; msum(a, n, 0) == 0;
  axiom msum_step: \forall int *a, integer n, integer rows; rows >= 0 ==> msum(a, n, rows+1) == msum(a, n, rows) + rsum(a + rows*n, n);
  lemma total: \forall int *a, integer n; n >= 1 && (\forall integer r, c; 0 <= r < n && 0 <= c < n ==> (r > c ==> 0 <= a[(r)*n + (c)] <= 1) && (r <= c ==> a[(r)*n + (c)] == 0)) ==> 2*(msum(a, n, n)) <= n*(n-1);
} */
int main()
{
	ARR_SIZE = (signed long long)__VERIFIER_nondet_short() ;
	assume_abort_if_not(ARR_SIZE > 0) ;

	int array[ARR_SIZE][ARR_SIZE] ;
	
	int row = 0, column = 0, num = -1;
       	signed long long sum = 0 ;
	int temp ;
	short index1,index2 ;

	/*@ loop invariant 0 <= row <= ARR_SIZE;
	    loop invariant \forall integer r, c; 0 <= r < row && 0 <= c < ARR_SIZE ==> array[r][c] == 0;
	    loop assigns row, column, array[0..ARR_SIZE-1][0..ARR_SIZE-1]; */
	for(row=0;row<ARR_SIZE;row++)
		/*@ loop invariant 0 <= column <= ARR_SIZE;
		    loop invariant 0 <= row < ARR_SIZE;
		    loop invariant \forall integer r, c; 0 <= r < row && 0 <= c < ARR_SIZE ==> array[r][c] == 0;
		    loop invariant \forall integer c; 0 <= c < column ==> array[row][c] == 0;
		    loop assigns column, array[row][0..ARR_SIZE-1]; */
		for(column=0;column<ARR_SIZE;column++)
			array[row][column] = 0 ;

	/*@ loop invariant \forall integer r, c; 0 <= r < ARR_SIZE && 0 <= c < ARR_SIZE ==> (r > c ==> 0 <= array[r][c] <= 1) && (r <= c ==> array[r][c] == 0);
	    loop assigns index1, index2, temp, array[0..ARR_SIZE-1][0..ARR_SIZE-1]; */
	while(1)
        {
		
		index1 = __VERIFIER_nondet_short() ;
		index2 = __VERIFIER_nondet_short() ;
		assume_abort_if_not(index1>=0 && index1 < ARR_SIZE) ;
		assume_abort_if_not(index2>=0 && index2 < ARR_SIZE) ;

		array[index1][index2] = (index1 > index2) ? (num*num*num*num) : array[index1][index2] ;
		

		temp = __VERIFIER_nondet_int() ;
		if(temp == 0) break ;
	}

	/*@ loop invariant 0 <= row <= ARR_SIZE;
	    loop invariant \forall integer r, c; 0 <= r < ARR_SIZE && 0 <= c < ARR_SIZE ==> (r > c ==> 0 <= array[r][c] <= 1) && (r <= c ==> array[r][c] == 0);
	    loop invariant sum == msum((int *) array, ARR_SIZE, row);
	    loop assigns row, column, sum; */
	for(row=0;row<ARR_SIZE;row++)
		/*@ loop invariant 0 <= column <= ARR_SIZE;
		    loop invariant 0 <= row < ARR_SIZE;
		    loop invariant \forall integer r, c; 0 <= r < ARR_SIZE && 0 <= c < ARR_SIZE ==> (r > c ==> 0 <= array[r][c] <= 1) && (r <= c ==> array[r][c] == 0);
		    loop invariant sum == msum((int *) array, ARR_SIZE, row) + rsum(array[row], column);
		    loop assigns column, sum; */
		for(column=0;column<ARR_SIZE;column++)
			sum = sum + array[row][column] ;

	__VERIFIER_assert(2*sum <= ARR_SIZE*(ARR_SIZE-1)) ;
	return 0 ;
}

		
