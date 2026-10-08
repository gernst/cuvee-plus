package util

// relations of a collection to a set that do not compute their intersection
extension [A](self: Iterable[A])
  infix def disjoint(that: Set[A]): Boolean =
    self.forall(!that.contains(_))

  infix def intersects(that: Set[A]): Boolean =
    self.exists(that.contains)
