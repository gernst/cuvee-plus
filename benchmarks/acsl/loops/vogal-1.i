// ACSL annotations added by hand (benchmarks/acsl/README.md): the counts are related by the logic function cnt of the axiomatic Count
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "vogal-1.c", 3, __extension__ __PRETTY_FUNCTION__); })); }

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
char __VERIFIER_nondet_char();

/*@ axiomatic Count {
  logic integer cnt(char *s, integer n);
  axiom cnt_zero: \forall char *s; cnt(s, 0) == 0;
  axiom cnt_step: \forall char *s, integer n; n > 0 ==>
    cnt(s, n) == cnt(s, n-1) + (s[n-1] == 'a' || s[n-1] == 'A' ? 1 : 0);
} */
int main(void)
{
  char input_string[5], vogal_array[]={'a','A','e','E','i','I','o','O','u','U','\0'};;
  unsigned int i,j,cont, tam_string, n_caracter;

  /*@ loop invariant 0 <= i <= 5;
      loop assigns i, input_string[0..4]; */
  for(i=0;i<5;i++)
    input_string[i] = __VERIFIER_nondet_char();
  if (!(input_string[5 -1]=='\0')) return 0;

  n_caracter = 0;
  /*@ loop invariant 0 <= n_caracter <= 4;
      loop invariant \forall integer t; 0 <= t < n_caracter ==> input_string[t] != '\0';
      loop assigns n_caracter; */
  while(input_string[n_caracter]!='\0')
    n_caracter++;

  cont = 0;
  /*@ loop invariant 0 <= i <= n_caracter;
      loop invariant vogal_array[0] == 'a' && vogal_array[1] == 'A';
      loop invariant cont == cnt(input_string, i);
      loop assigns i, j, cont; */
  for(i=0;i<n_caracter;i++)
     /*@ loop invariant 0 <= j <= 2;
         loop invariant vogal_array[0] == 'a' && vogal_array[1] == 'A';
         loop invariant cont == cnt(input_string, i) + (j >= 1 && input_string[i] == 'a' ? 1 : 0) + (j >= 2 && input_string[i] == 'A' ? 1 : 0);
         loop assigns j, cont; */
     for(j=0;j<5/2;j++)
        if(input_string[i] == vogal_array[j])
           cont++;

  i=0;
  int cont_aux = 0;
  /*@ loop invariant 0 <= i <= n_caracter;
      loop invariant \forall integer t; 0 <= t < n_caracter ==> input_string[t] != '\0';
      loop invariant input_string[n_caracter] == '\0';
      loop invariant vogal_array[0] == 'a' && vogal_array[1] == 'A';
      loop invariant cont_aux == cnt(input_string, i);
      loop assigns i, j, cont_aux; */
  while(input_string[i]!='\0')
  {
    /*@ loop invariant 0 <= j <= 2;
        loop invariant vogal_array[0] == 'a' && vogal_array[1] == 'A';
        loop invariant cont_aux == cnt(input_string, i) + (j >= 1 && input_string[i] == 'a' ? 1 : 0) + (j >= 2 && input_string[i] == 'A' ? 1 : 0);
        loop assigns j, cont_aux; */
    for(j=0;j<5/2;j++)
    {
        if(input_string[i] == vogal_array[j])
           cont_aux++;
    }
    i++;
  }
  __VERIFIER_assert(cont_aux==cont);

  return 0;
}
