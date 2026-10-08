// ./Cuvee.sh examples/c/printing/names.c
// names of the input that end like those of temporaries are kept apart from them
int f(void); int main(void) { int tmp_1 = 2; int r = tmp_1 + f(); return r; }
