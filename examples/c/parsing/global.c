// ./Cuvee.sh -quiet examples/c/parsing/global.c
// the initial values are the precondition of main, they must not call functions
int g = 1; int main(void) { return g; }
