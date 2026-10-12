// ACSL annotations added by hand (benchmarks/acsl/README.md): the total of the two sums is a loop invariant (each iteration adds count and -count at zero positions, lemma asum_update)
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
 * Two arrays are declared of same size. All elements are initialized to 0.
 * In while(1) loop, two indicies are selected non-deterministically, whose entries in array are zero.
 * Array1[index1] is initialized with count.
 * Array2[index2] is initialized with -count.
 * Sum of both array should be always zero.
 * Changelog --> 22 November 2019
 * Variable count is reset on reaching 200. One can have any other integer value as well
 * to reset count. It is an additional challenge for Tools/solvers using supervised learning
 * based techniques for algorithm selection. 200 is the max unrolling for most of the reachsafe
 * programs to reach property violation. Presence of 200 as part of statement assignment 
 * inside loop can be picked up by algorithm selector to deploy only falsification/correctness proving
 * techniques.
 
 * */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array4_pattern.c", 35, "reach_error"); }
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

/*@ axiomatic Asum {
  logic integer asum(int *a, integer n) reads a[0..n-1];
  axiom asum_zero: \forall int *a; asum(a, 0) == 0;
  axiom asum_step: \forall int *a, integer n; n >= 0 ==> asum(a, n+1) == asum(a, n) + a[n];
  logic integer sqsum(int *a, integer n) reads a[0..n-1];
  axiom sqsum_zero: \forall int *a; sqsum(a, 0) == 0;
  axiom sqsum_step: \forall int *a, integer n; n >= 0 ==> sqsum(a, n+1) == sqsum(a, n) + a[n]*a[n];
  lemma asum_update{L1, L2}: \forall int *a, integer n, k; 0 <= k < n && (\forall integer t; 0 <= t < n && t != k ==> \at(a[t], L2) == \at(a[t], L1)) ==> \at(asum(a, n), L2) == \at(asum(a, n), L1) + \at(a[k], L2) - \at(a[k], L1);
} */
int main()
{
	ARR_SIZE = __VERIFIER_nondet_short() ;
	assume_abort_if_not(ARR_SIZE > 0) ;

	int array1[ARR_SIZE] ;
	int array2[ARR_SIZE] ;
	int count = 0, num = -1 ;
        signed long long sum = 0 ;
	int temp ;
	short index1,index2 ;

	/*@ loop invariant 0 <= count <= ARR_SIZE;
	    loop invariant \forall integer t; 0 <= t < count ==> array1[t] == 0 && array2[t] == 0;
	    loop assigns count, array1[0..ARR_SIZE-1], array2[0..ARR_SIZE-1]; */
	for(count=0;count<ARR_SIZE;count++)
	{
		array1[count] = 0 ;
		array2[count] = 0 ;
	}

	count = 1 ;

	/*@ loop invariant asum(array1, ARR_SIZE) + asum(array2, ARR_SIZE) == 0;
	    loop invariant 1 <= count <= 200;
	    loop assigns index1, index2, temp, count, array1[0..ARR_SIZE-1], array2[0..ARR_SIZE-1]; */
	while(1)
        {
		
		index1 = __VERIFIER_nondet_short() ;
		index2 = __VERIFIER_nondet_short() ;
		assume_abort_if_not(index1>=0 && index1 < ARR_SIZE) ;
		assume_abort_if_not(index2>=0 && index2 < ARR_SIZE) ;
		assume_abort_if_not(array1[index1] == 0) ;
		assume_abort_if_not(array2[index2] == 0) ;

		array1[index1] = num * (num * count) ;
		array2[index2] = num * count ;
		if(count == 200)
			count = 0 ;
		count++ ;

		temp = __VERIFIER_nondet_int() ;
		if(temp == 0) break ;
	}

	/*@ loop invariant 0 <= count <= ARR_SIZE;
	    loop invariant asum(array1, ARR_SIZE) + asum(array2, ARR_SIZE) == 0;
	    loop invariant sum == asum(array1, count) + asum(array2, count);
	    loop assigns count, sum; */
	for(count=0;count<ARR_SIZE;count++)
	{
		sum = sum  + array1[count] + array2[count];
	}

	__VERIFIER_assert(sum == 0) ;
	return 0 ;
}

		
