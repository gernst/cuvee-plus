// ACSL annotations added by hand (benchmarks/acsl/README.md): SelectionSort sorts the global array, main checks its local array of the same name
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

/*@ requires \false;
    assigns \nothing; */
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "eureka_05.c", 3, __extension__ __PRETTY_FUNCTION__); })); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}



int array[5];
int n=5;

/*@ requires n == 5;
    assigns array[0..n-1]; */
void SelectionSort()
{
   int lh, rh, i, temp;

   /*@ loop invariant 0 <= lh <= n;
       loop assigns lh, rh, i, temp, array[0..n-1]; */
   for (lh = 0; lh < n; lh++) {
      rh = lh;
      /*@ loop invariant lh <= rh < n;
          loop invariant lh+1 <= i <= n;
          loop assigns i, rh; */
      for (i = lh + 1; i < n; i++)
         if (array[i] < array[rh]) rh = i;
      temp = array[lh];
      array[lh] = array[rh];
      array[rh] = temp;
   }
}

int main(void){

 int array[5],i;

 /*@ loop invariant -1 <= i <= 4;
     loop invariant \forall integer t; i < t < 5 ==> array[t] == t;
     loop assigns i, array[0..4]; */
 for(i=5 -1; i>=0; i--)
  array[i]=i;

 SelectionSort();

 /*@ loop invariant 0 <= i <= 5;
     loop invariant \forall integer t; 0 <= t < 5 ==> array[t] == t;
     loop assigns i; */
 for(i=0; i<5; i++)
  __VERIFIER_assert(array[i]==i);

}
