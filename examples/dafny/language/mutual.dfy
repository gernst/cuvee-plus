// ./Cuvee.sh examples/dafny/language/mutual.dfy
// consecutive datatypes may refer to each other, also to later ones, as in Dafny;
// each group of mutually recursive ones is declared together, after those that it refers to
datatype Box = box(t: Tree<int>)

datatype Tree<a> = node(value: a, children: Forest<a>)

datatype Forest<a> = leaf | grow(first: Tree<a>, rest: Forest<a>)

function root(b: Box): int
{
  Tree_value(Box_t(b))
}
