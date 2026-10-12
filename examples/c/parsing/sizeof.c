// ./Cuvee.sh -vcgen -z3 examples/c/parsing/sizeof.c
// the sizes of integer types are those of the data models ILP32 (-arch 32) and LP64 (-arch 64, the default)
typedef unsigned int size_t; int main(void) { assert(sizeof(int) == 4 && sizeof(unsigned long long) == 8 && sizeof(char) == 1 && sizeof(short int) == 2 && sizeof(size_t) == 4); return 0; }
