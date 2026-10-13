package cuvee.prove

import cuvee.core._

object Classes:
  def empty(constrs: Set[Fun]) =
    Classes(constrs, Map(), Map(), Map(), Nil)

// congruence closure over the terms of the facts: a persistent union-find whose nodes are the registered terms, where
// applications are decomposed into their arguments and everything else (variables, literals, binders, the combinators
// of trace equation systems) is a node of its own; two applications of the same function to arguments of the same
// classes are merged (congruence); the theory replaces the chains of variable equations of the simplifier: the
// definitions of a variable are the other members of its class, which the matcher follows in any position, both
// orientations of an equation are available, and equal terms are identified transitively, e.g. two counters K == I
//
// parent: the union-find, every registered term maps to itself or to a term of its class;
// members: the members of each class by its root;
// uses: the applications that have a member of the class as a direct argument, by root;
// diseqs: the disequations among the facts, which contradict the classes once their sides are in one class;
// two different literals or two applications of different constructors in one class are inconsistent as well
case class Classes(
    constrs: Set[Fun],
    parent: Map[Expr, Expr],
    members: Map[Expr, List[Expr]],
    uses: Map[Expr, List[Expr]],
    diseqs: List[(Expr, Expr)]
) extends Theory:
  def find(expr: Expr): Expr =
    parent.get(expr) match
      case Some(next) if next != expr => find(next)
      case _                          => expr

  // the members of the class of `expr`, itself if it is not registered
  def classOf(expr: Expr): List[Expr] =
    members.getOrElse(find(expr), List(expr))

  def equal(a: Expr, b: Expr): Boolean =
    a == b || (parent.contains(a) && parent.contains(b) && find(a) == find(b))

  // the definitions of `expr`: the members of its class that are not variables, except itself
  def defs(expr: Expr): List[Expr] =
    classOf(expr).filter(e => e != expr && !e.isInstanceOf[Var])

  // the literal of the class, if it has one
  def literal(expr: Expr): Option[Lit] =
    classOf(expr).collectFirst { case lit: Lit => lit }

  // the canonical variable of the class of a variable, the smallest one by name, such that equal variables are
  // replaced consistently (the replace of the chains of the simplifier)
  def canonical(x: Var): Var =
    classOf(x).collect { case y: Var => y }.minByOption(y => (y.name.name, y.name.index.getOrElse(-1))).getOrElse(x)

  lazy val inconsistent: Boolean =
    diseqs.exists((a, b) => equal(a, b)) || members.values.exists(clashes)

  // two different literals, or two applications of different constructors
  def clashes(members: List[Expr]): Boolean =
    val lits = members.collect { case lit: Lit => lit }.distinct
    val cons = members.collect { case App(fun, _, _, _) if constrs.contains(fun) => fun }.distinct
    lits.length > 1 || cons.length > 1

  def free: Set[Var] =
    parent.keySet.collect { case x: Var => x }

  // all terms of a fact are registered, such that their classes are known, equations merge, disequations are kept
  def assume(expr: Expr): Classes =
    expr match
      case Eq(a, b)      => merge(a, b)
      case Not(Eq(a, b)) => add(a).add(b).copy(diseqs = (a, b) :: diseqs)
      case Not(phi)      => add(phi)
      case _             => add(expr)

  def deny(expr: Expr): Classes =
    expr match
      case Eq(a, b)      => add(a).add(b).copy(diseqs = (a, b) :: diseqs)
      case Not(Eq(a, b)) => merge(a, b)
      case Not(phi)      => add(phi)
      case _             => add(expr)

  def congruent(a: Expr, b: Expr): Boolean =
    (a, b) match
      case (App(f, i, _, as), App(g, j, _, bs)) =>
        f == g && i == j && as.length == bs.length && (as zip bs).forall((x, y) => find(x) == find(y))
      case _ =>
        false

  // a new term and its arguments, which is merged with an application that is congruent to it
  def add(expr: Expr): Classes =
    if parent.contains(expr)
    then this
    else
      val added = copy(parent = parent + (expr -> expr), members = members + (expr -> List(expr)))
      expr match
        case App(_, _, _, args) if args.nonEmpty =>
          val withArgs = args.foldLeft(added)(_.add(_))
          val withUses = args.foldLeft(withArgs): (cl, arg) =>
            val root = cl.find(arg)
            cl.copy(uses = cl.uses + (root -> (expr :: cl.uses.getOrElse(root, Nil))))
          withUses.uses.getOrElse(withUses.find(args.head), Nil).find(u => u != expr && withUses.congruent(u, expr)) match
            case Some(u) => withUses.merge(u, expr)
            case None    => withUses

        case _ =>
          added

  // the classes of a and b are merged, the smaller one into the larger, after which the applications over the
  // smaller class may be congruent to those over the larger one, which are merged in turn
  def merge(a: Expr, b: Expr): Classes =
    val cl = add(a).add(b)
    val ra = cl.find(a)
    val rb = cl.find(b)
    if ra == rb
    then cl
    else
      val (small, big) = if cl.members(ra).length <= cl.members(rb).length then (ra, rb) else (rb, ra)
      val usesSmall = cl.uses.getOrElse(small, Nil)
      val usesBig = cl.uses.getOrElse(big, Nil)
      val merged = cl.copy(
        parent = cl.parent + (small -> big),
        members = cl.members - small + (big -> (cl.members(big) ++ cl.members(small))),
        uses = cl.uses - small + (big -> (usesBig ++ usesSmall))
      )
      val pairs = for u <- usesSmall; v <- usesBig if merged.congruent(u, v) yield (u, v)
      pairs.foldLeft(merged)((cl, pair) => cl.merge(pair._1, pair._2))
