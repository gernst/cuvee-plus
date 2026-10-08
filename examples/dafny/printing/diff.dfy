// ./Cuvee.sh examples/dafny/printing/diff.dfy
// derivatives are printed with their variables
function f(x: real, y: real): bool { (x :: x)' == (x, y :: x * y)' && -(x :: x)' == 0.0 }
