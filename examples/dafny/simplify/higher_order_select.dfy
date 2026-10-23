// ./Cuvee.sh -prove examples/dafny/simplify/higher_order_select.dfy
// the higher-order variable G of the rule matches a[i] by the lambda (z) => a[z] of function type, which is not the
// array a (eta reduction is for lambdas of array type only), such that G(i) on the right-hand side is a[i] again
function g(i: int, x: int): int

lemma {:rw} g_def(i: int, G: (int) -> int)
  ensures g(i, G(i)) == G(i) + 1

function f(a: array<int, int>, i: int): int
{
  g(i, a[i])
}
