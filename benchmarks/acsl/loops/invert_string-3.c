// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "invert_string-3.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
char __VERIFIER_nondet_char();

int main() {
    unsigned int max = 5;
    char str1[max], str2[max];
    int i, j;

    /*@ loop invariant 0 <= i <= max;
        loop assigns i, str1[0..max-1]; */
    for (i=0; i<max; i++) {
        str1[i]=__VERIFIER_nondet_char();
    }

    str1[max-1]= '\0';

    j = 0;
   
    /*@ loop invariant -1 <= i <= max-1;
        loop invariant j == max-1-i;
        loop invariant \forall integer t; 0 <= t < j ==> str2[t] == str1[max-1-t];
        loop assigns i, j, str2[0..max-1]; */
    for (i = max - 1; i >= 0; i--) {
        str2[j] = str1[i];
        j++;
    }

    j = max-1;
    /*@ loop invariant 0 <= i <= max;
        loop invariant j == max-1-i;
        loop invariant \forall integer t; 0 <= t < max ==> str2[t] == str1[max-1-t];
        loop assigns i, j; */
    for (i=0; i<max; i++) {
      __VERIFIER_assert(str1[i] == str2[j]);
      j--;
    }   
}

