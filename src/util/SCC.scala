package util

// the strongly connected components of the graph of `nodes` with the successors `succ` of each node,
// where successors that are not among `nodes` are ignored,
// each component after those that it reaches, and otherwise in the order of `nodes`, also within components
object SCC:
  def apply[A](nodes: List[A], succ: A => Set[A]): List[List[A]] =
    val edges = nodes.map(n => n -> nodes.filter(succ(n)).toSet).toMap

    // the nodes reachable from each one
    def reach(todo: List[A], seen: Set[A]): Set[A] =
      todo match
        case Nil                          => seen
        case n :: rest if seen contains n => reach(rest, seen)
        case n :: rest                    => reach(edges(n).toList ++ rest, seen + n)

    val reachable = nodes.map(n => n -> reach(edges(n).toList, Set())).toMap
    val components = nodes.map(n => nodes.filter(m => m == n || reachable(n)(m) && reachable(m)(n))).distinct

    def order(todo: List[List[A]], done: List[List[A]]): List[List[A]] =
      todo match
        case Nil => done
        case _ =>
          val emitted = done.flatten.toSet
          val next = todo.find(c => c.forall(n => (reachable(n) -- c).subsetOf(emitted))).get
          order(todo.filterNot(_ == next), done :+ next)

    order(components, Nil)
