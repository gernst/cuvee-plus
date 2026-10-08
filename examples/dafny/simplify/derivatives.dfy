// ./Cuvee.sh -simplify examples/dafny/simplify/derivatives.dfy
// derivatives (x, y :: e)' by the rules of dL: constants, variables, sums, the product rule, comparisons, and conjunctions,
// the chain rule for other functions is not applied
function f(x: real): real
function d1(x: real, y: real, c: real): real { (x :: c + 2.0)' }
function d2(x: real, y: real, c: real): real { (x :: x)' }
function d3(x: real, y: real, c: real): real { (x, y :: x + y)' }
function d4(x: real, y: real, c: real): real { (x :: x - c)' }
function d5(x: real, y: real, c: real): real { (x, y :: x * y)' }
function d6(x: real, y: real, c: real): real { (x :: c * x)' }
function d7(x: real, y: real, c: real): bool { (x :: x < c)' }
function d8(x: real, y: real, c: real): bool { (x, y :: x == c * y)' }
function d9(x: real, y: real, c: real): bool { (x, y :: c <= x < y)' }
function d10(x: real, y: real, c: real): real { (x :: f(x))' }
