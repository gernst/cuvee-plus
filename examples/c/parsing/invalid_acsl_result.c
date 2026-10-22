// ./Cuvee.sh -quiet examples/c/parsing/invalid_acsl_result.c
// \result is the result in postconditions only
/*@ requires \result > 0; */
int f(void) { return 1; }
int main(void) { return f(); }
