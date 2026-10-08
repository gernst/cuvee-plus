// ./Cuvee.sh -print null examples/c/parsing/conditions.c
// conversions between integers and truth values
int f(int x) { if (x) return !x; else return x && 1; }
