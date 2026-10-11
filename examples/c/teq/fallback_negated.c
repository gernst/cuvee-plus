// ./Cuvee.sh -unbounded -teq -simplify -split -simplify -fallback examples/c/teq/fallback_negated.c
// with -unbounded, since -teq does not accelerate unsigned counters, which wrap around otherwise
// the loop of SV-COMP loop-acceleration/simple_3-1, whose goal is a negated conjunction, since the assertion fails:
// the equations of the counters are hypotheses there as well, which determine the lengths of the traces
int main(void) { unsigned int x = 0; unsigned int N; while (x < N) { x += 2; } assert(x % 2); return 0; }
