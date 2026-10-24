package cuvee.prove

import cuvee.core._

object Classes:
  def empty(constrs: Set[Fun]) =
    Classes(constrs, Map(), Map(), Map(), Nil, false)

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
// (clashed, checked when classes are merged)
case class Classes(
    constrs: Set[Fun],
    parent: Map[Expr, Expr],
    members: Map[Expr, List[Expr]],
    uses: Map[Expr, List[Expr]],
    diseqs: List[(Expr, Expr)],
    clashed: Boolean
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
  // replaced consistently (the replace of the chains of the simplifier); the root of the class unless it has a
  // literal (see rank)
  def canonical(x: Var): Var =
    find(x) match
      case y: Var => y
      case _      => classOf(x).collect { case y: Var => y }.minByOption(y => (y.name.name, y.name.index.getOrElse(-1))).getOrElse(x)

  lazy val inconsistent: Boolean =
    clashed || diseqs.exists((a, b) => equal(a, b))

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

  // the term with its registered subterms replaced by the roots of their classes, bottom-up, such that terms that
  // the classes identify become syntactically equal, also below binders, which the classes do not decompose (see
  // Rewrite.known); bound variables are not registered, since they are renamed apart from the context
  def normalize(expr: Expr): Expr =
    val expr_ = expr.map(normalize)
    if parent.contains(expr_) then find(expr_) else expr_

  // whether `outer` contains `inner` as a proper subterm modulo the classes, both normalized, but not as it is: a
  // rewrite of `inner` to such an `outer` leads back to its own term through the classes, e.g. integer(n7) to
  // -integer(n25) + ... with n25 == n7, which the simplifier turns into integer(n7) again (see Rewrite.applyActive); a
  // result equal to the term modulo the classes, e.g. its literal, is no such cycle, and a result that contains the
  // term as it is, e.g. of a rule f(x) == f(f(x)), is left to the bound on the steps, which reports the rule
  def within(inner: Expr, outer: Expr): Boolean =
    def occurs(inner: Expr, expr: Expr): Boolean =
      expr == inner || {
        var found = false
        expr.map { arg => found = found || occurs(inner, arg); arg }
        found
      }
    val inner_ = normalize(inner)
    val outer_ = normalize(outer)
    outer_ != inner_ && occurs(inner_, outer_) && !occurs(inner, outer)

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

  // the rank of a root: a literal before a variable before any other term, variables by name, such that the root of a
  // class is the representative that the simplifier uses (see canonical and Simplify.var_) and normalize gives the
  // same, rather than whichever root the order of the merges left (see merge)
  def rank(expr: Expr): (Int, String, Int) =
    expr match
      case _: Lit => (0, "", 0)
      case x: Var => (1, x.name.name, x.name.index.getOrElse(-1))
      case _      => (2, "", 0)

  // the classes of a and b are merged, the smaller one into the larger, after which the applications over the
  // smaller class may be congruent to those over the larger one, which are merged in turn; the root of the merged
  // class is the one of lower rank, the larger class's if they tie, and the members keep the order of the larger
  // class first, which is the order in which the definitions are tried (see Context.defs)
  def merge(a: Expr, b: Expr): Classes =
    val cl = add(a).add(b)
    val ra = cl.find(a)
    val rb = cl.find(b)
    if ra == rb
    then cl
    else
      val (small, big) = if cl.members(ra).length <= cl.members(rb).length then (ra, rb) else (rb, ra)
      val (child, root) = if Ordering[(Int, String, Int)].lt(rank(small), rank(big)) then (big, small) else (small, big)
      val usesSmall = cl.uses.getOrElse(small, Nil)
      val usesBig = cl.uses.getOrElse(big, Nil)
      val members_ = cl.members(big) ++ cl.members(small)
      val merged = cl.copy(
        parent = cl.parent + (child -> root),
        members = cl.members - small - big + (root -> members_),
        uses = cl.uses - small - big + (root -> (usesBig ++ usesSmall)),
        clashed = cl.clashed || clashes(members_)
      )
      val pairs = for u <- usesSmall; v <- usesBig if merged.congruent(u, v) yield (u, v)
      pairs.foldLeft(merged)((cl, pair) => cl.merge(pair._1, pair._2))
