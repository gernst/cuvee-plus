// ./Cuvee.sh -prove examples/dafny/prove/negated_conjunctions.dfy
// a goal of several negated conjunctions is normalized once: the negations moved to the succedents are taken in their
// order, otherwise the goal came back reordered and was normalized again without end; the goal does not hold
lemma negated(x: int, y: int, c: int, d: int)
  ensures !(x == c && d == c) && !(y == c && d == c)
