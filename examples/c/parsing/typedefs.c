// ./Cuvee.sh -vcgen -z3 examples/c/parsing/typedefs.c
// the names of types are replaced by their definitions, which fail only where they are used
typedef unsigned int size_t; typedef size_t index; __extension__ typedef long long int big; int main(void) { index i = 3; big b = (big) i * 2; assert(b == 6); return 0; }
