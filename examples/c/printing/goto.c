// ./Cuvee.sh examples/c/printing/goto.c
// a goto whose label marks a statement that does not fall through is that statement in its place: a return, the
// error block of SV-COMP, the end of the function body; a label of a goto to itself is a loop without exit
extern void abort(void);
void reach_error() {}
int f(int x) {
  if (x < 0) goto NEG;
  if (x == 0) goto STUCK;
  x = x - 1;
  return x;
NEG:
  return 0;
STUCK:
  goto STUCK;
}
void g(int y) {
  if (y > 10) goto END;
  if (y < -10) goto ERROR;
  y = y + 1;
  return;
ERROR: { reach_error(); abort(); }
END:
  ;
}
