// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "insertion_sort-2-2.c", 3, "reach_error"); }

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
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();
int main() {
   unsigned int SIZE=__VERIFIER_nondet_uint();
   if (SIZE >= 4000000000 / sizeof(int)) {
     return 0;
   }
   int i, j, k, key;
   int v[SIZE];   
   /*@ loop invariant 0 <= j <= SIZE;
       loop assigns j, v[0..SIZE-1]; */
   for (j=0;j<SIZE;j++)
      v[j] = __VERIFIER_nondet_int();
   /*@ loop invariant (SIZE == 0 && j == 1) || 1 <= j <= SIZE;
       loop invariant \forall integer p, q; 0 <= p < q < j ==> v[p] <= v[q];
       loop assigns j, i, key, v[0..SIZE-1]; */
   for (j=1;j<SIZE;j++) {	  
      key = v[j];
      i = j - 1;
      /*@ loop invariant -1 <= i <= j-1;
          loop invariant \forall integer p, q; 0 <= p < q <= j && p != i+1 && q != i+1 ==> v[p] <= v[q];
          loop invariant \forall integer p; i+2 <= p <= j ==> v[p] > key;
          loop assigns i, v[0..j]; */
      while((i>=0) && (v[i]>key)) {
         v[i+1] = v[i];
         i = i - 1;
      }
      v[i+1] = key;	        
  }      
  /*@ loop invariant (SIZE == 0 && k == 1) || 1 <= k <= SIZE;
      loop invariant \forall integer p, q; 0 <= p < q < SIZE ==> v[p] <= v[q];
      loop assigns k; */
  for (k=1;k<SIZE;k++)
    __VERIFIER_assert(v[k-1]<=v[k]);  
   return 0;
}

