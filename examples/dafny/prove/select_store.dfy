// ./Cuvee.sh -prove examples/dafny/prove/select_store.dfy
// a read after a write at another index: decided by the facts, e.g. j != 3 (single_elem_safe), and, where nothing
// decides the equation of the indices, by the cases i == j and i != j of the goal (Prove.alternatives)

lemma other(a: array<int, int>, w: int, j: int)
  requires j != 3
  ensures a[3 := w][j] == a[j]
{
}

lemma cases(a: array<int, int>, i: int, j: int, v: int)
  ensures a[i := v][j] == v || a[i := v][j] == a[j]
{
}
