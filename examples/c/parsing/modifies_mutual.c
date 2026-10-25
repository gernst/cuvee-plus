// ./Cuvee.sh -print dfy examples/c/parsing/modifies_mutual.c
// the modifies clauses of functions that call each other are a fixpoint over their bodies, which are resolved before
// they are checked: even and odd modify g, which odd assigns, and h, which the loop of even assigns; a parameter with
// the name of a global variable is renamed apart, since local variables must not shadow global ones
int g; int h;
int odd(int n);
int even(int n) { while (h < n) { h = h + 1; } if (n == 0) return 1; return odd(n - 1); }
int odd(int n) { g = n; if (n == 0) return 0; return even(n - 1); }
int get(int g) { return g + h; }
