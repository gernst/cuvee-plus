// ./Cuvee.sh -verify -z3 examples/c/parsing/literals.c
int main(void) { assert(0x1F == 31); assert(010 == 8); assert(7UL == 7); assert(0xffffffffu == 4294967295LL); assert('a' == 97); assert('\n' == 10); assert('\0' == 0); assert('\x41' == 65); assert('\'' == 39); return 0; }
