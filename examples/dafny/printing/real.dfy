// ./Cuvee.sh -simplify examples/dafny/printing/real.dfy
// real literals have a decimal point, fractions without finite decimal expansion are divisions
function f(x: real): seq<real> { [2.0, -1.5, 1.0 / 3.0, -1.0 / 3.0, 1.0 / 3.0 * x] }
