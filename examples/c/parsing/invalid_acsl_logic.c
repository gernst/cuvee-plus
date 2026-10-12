// ./Cuvee.sh -print null examples/c/parsing/invalid_acsl_logic.c
// a logic function must not be named like a function of the program
/*@ logic integer f(integer x) = x + 1; */
int f(int x) { return x + 1; }
int main(void) { return f(0); }
