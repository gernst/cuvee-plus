package cuvee.prove

import cuvee.core._

object Classes:
  def empty(constrs: Set[Fun]) =
    Classes(constrs, Map(), Map(), Map(), Nil, false)

  type Rank = (Int, Int, Int, Int, String)

  // the order of the roots, given by the context (see Context.order): a literal before a variable before any other
  // term, variables by the depth of the scope that binds them and their position in it, then by index and name; the
  // root of a class is its least member, and an equation is solved for its greatest variable (see solve), so that the
  // canonical forms write the variables of inner scopes by those of outer ones, and those of a binder by the earlier
  // ones, e.g. the position i == k + 1 of a loop by the counter k of its iterations
  case class Order(rank: Expr => Rank)

  def rank(scope: Var => (Int, Int))(expr: Expr): Rank =
    expr match
      case _: Lit => (0, 0, 0, 0, "")
      case x: Var =>
        val (depth, position) = scope(x)
        (1, depth, position, x.name.index.getOrElse(-1), x.name.name)
      case _ => (2, 0, 0, 0, "")

// congruence closure over the terms of the facts: a persistent union-find whose nodes are the registered terms, where
// applications are decomposed into their arguments and everything else (variables, literals, binders, the combinators
// of trace equation systems) is a node of its own; two applications of the same function to arguments of the same
// classes are merged (congruence); the definitions of a variable are the other members of its class, which the
// matcher follows in any position and orientation, e.g. two counters K == I; with the solutions of linear equations
// (solved), the classes give the canonical forms of terms (normalize), Shostak-style
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
    clashed: Boolean,
    solved: Map[Var, Expr] = Map(),
    merges: Int = 0,
    retired: List[Expr] = Nil
) extends Theory:
  // solved: the solutions of linear equations by variable (see solve); merges: the number of merges and solutions,
  // retired: the roots that they changed, newest first, by which the context renormalizes those of its facts that
  // mention them, the others are canonical already (see Context.assume)
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
  def assume(expr: Expr)(using order: Classes.Order): Classes =
    expr match
      case Eq(a, b)      => merge(a, b).solve(a, b)
      case Not(Eq(a, b)) => add(a).add(b).copy(diseqs = (a, b) :: diseqs)
      case Not(phi)      => add(phi)
      case _             => add(expr)

  def deny(expr: Expr)(using order: Classes.Order): Classes =
    expr match
      case Eq(a, b)      => add(a).add(b).copy(diseqs = (a, b) :: diseqs)
      case Not(Eq(a, b)) => merge(a, b).solve(a, b)
      case Not(phi)      => add(phi)
      case _             => add(expr)

  // the solution of a linear equation for its greatest variable that is not solved yet, e.g. x by 40 - n for
  // n + x == 40, if it is arithmetic over variables (see Poly.solution); the variable is merged with its solution;
  // other terms, e.g. reads of traces or arrays, are never solutions, they stay members of their classes
  def solve(a: Expr, b: Expr)(using order: Classes.Order): Classes =
    Ring(a.typ) match
      case Some(ring) =>
        val poly = (Arith.toPoly(ring, a) - Arith.toPoly(ring, b)).normalize
        val solution =
          for
            (x, rest) <- poly.solution(order.rank, (x, rest) => !(solved contains x) && rest.monos.forall(_.atoms.forall(_._1.isInstanceOf[Var])))
            e = rest.toExpr(ring)
            if e.isArith
          yield (x, e)
        solution match
          case Some((x, e)) =>
            val cl = merge(x, e)
            cl.copy(solved = solved + (x -> e), merges = cl.merges + 1, retired = cl.find(x) :: x :: cl.retired)
          case None         => this
      case None =>
        this

  // the policy of canonical forms, the only operations by which the simplifier, the context and the matcher write
  // terms and facts over the classes (see ideas/engine.md, section 1):
  // term: how a variable is written in a term, the root of its class (a literal before a variable, see rank);
  // value: a leaf of a polynomial with the solutions of its variables (see substitute);
  // fixed: whether a variable has a literal value, which then is its root;
  // ground: a registered term whose class has a literal as its root by that literal, also an application, e.g. the
  // read a[i] under a[i] == 1 in the stored value a[i := a[i] + 1], which the facts with a literal are no rewrite rules
  // for (see Context.rule), so that writing them costs no rewrite step;
  // fact: the canonical form of a fact (see normalize)
  def term(x: Var): Expr =
    normalize(x)

  def ground(expr: Expr): Expr =
    if parent.contains(expr)
    then
      find(expr) match
        case lit: Lit => lit
        case _        => expr
    else expr

  def value(leaf: Expr): Expr =
    substitute(leaf)

  def fixed(x: Var): Boolean =
    find(x).isInstanceOf[Lit]

  def fact(phi: Expr): Expr =
    normalize(phi)

  // the canonical form of a term, bottom-up: arithmetic by its polynomial normal form, as the simplifier writes it, with
  // the solved variables among its atoms replaced by their solutions (see Simplify.poly), and a registered term by the
  // root of its class, such that terms that the classes identify become equal, also below binders, which the classes
  // do not decompose; solutions are substituted inside arithmetic only, so that a variable keeps its place elsewhere,
  // e.g. the index i of a store a[i := a[i - 1] + 2] where i == k + 1 gives a[i := a[k] + 2]; an arithmetic term
  // whose class has a solved variable as its root stays as it is; bound variables are not registered, since they are
  // renamed apart from the context; an equation of equal sides is true, e.g. a definition x == f(y) of the classes,
  // which the facts keep as it is (see Facts.map)
  def normalize(expr: Expr): Expr =
    normalize(expr, util.Ref(Map()))

  // the same with the normalized solutions of the variables met so far in this term, each computed once, since a chain
  // of solutions in each other is expanded again at every occurrence otherwise, exponentially in its length, e.g. the
  // values of x before and after x = x * (z - 1), each modulo 2^64 (geo1-ll)
  def normalize(expr: Expr, solutions: util.Ref[Map[Var, Option[Expr]]]): Expr =
    val expr_ = expr.map(normalize(_, solutions))
    val expr__ =
      expr_ match
        case Eq(a, b) if a == b =>
          True
        case _ if expr_.isArith =>
          Ring(expr_.typ) match
            case Some(ring) => Arith.toPoly(ring, expr_, substitute(_, solutions)).normalize.toExpr(ring)
            case None       => expr_
        case _ =>
          expr_
    if parent.contains(expr__) then
      find(expr__) match
        case y: Var if expr__.isArith && solution(y).isDefined => expr__
        case root                                              => root
    else expr__

  // a solved atom of a polynomial by the canonical form of its solution
  def substitute(expr: Expr): Expr =
    substitute(expr, util.Ref(Map()))

  // the same with the solutions normalized so far (see normalize), also the variables without a usable solution (None),
  // whose lookup costs a traversal of the classes as well (see acyclic); a variable whose solution is being normalized
  // is None meanwhile, so that it stays an atom where its solution leads back to it through the roots of the classes
  def substitute(expr: Expr, solutions: util.Ref[Map[Var, Option[Expr]]]): Expr =
    expr match
      case x: Var =>
        val entry =
          solutions.value.get(x) match
            case Some(entry) =>
              entry
            case None =>
              solutions := solutions.value + (x -> None)
              val entry = solution(x).map(normalize(_, solutions))
              solutions := solutions.value + (x -> entry)
              entry
        entry.getOrElse(x)
      case _ =>
        expr

  // the solution of a variable of the class of x (see solve), unless it depends on that variable (see acyclic)
  def solution(x: Var): Option[Expr] =
    classOf(x).iterator.flatMap {
      case y: Var => solved.get(y).filter(acyclic(y, _))
      case _      => None
    }.nextOption()

  // whether e does not depend on x through the classes, transitively, e.g. the solution of n by an expression over a
  // trace K with K == counter(0, 1, n), whose inlining would loop (see normalize, Simplify.var_)
  def acyclic(x: Var, e: Expr): Boolean =
    def reach(todo: List[Var], seen: Set[Var]): Set[Var] =
      todo match
        case Nil                          => seen
        case y :: rest if seen contains y => reach(rest, seen)
        case y :: rest =>
          val next = classOf(y).flatMap(_.free).toList
          reach(next ++ rest, seen + y)

    !reach(e.free.toList, Set()).contains(x)

  // whether `outer` contains `inner` as a proper subterm modulo the classes, both normalized, but not as it is: a
  // rewrite of `inner` to such an `outer` leads back to its own term through the canonical forms, e.g. f(n7) to
  // -f(n25) + ... with n25 == n7 (see Rewrite.applyActive); a result equal to the term modulo the classes, e.g. its
  // literal, is no such cycle, and one that contains the term as it is, e.g. of a rule f(x) == f(f(x)), is left to
  // the bound on the steps
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
  def add(expr: Expr)(using order: Classes.Order): Classes =
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
  // smaller class may be congruent to those over the larger one, which are merged in turn; the root of the merged
  // class is the one of lower rank, the larger class's if they tie, and the members keep the order of the larger
  // class first, which is the order in which the definitions are tried (see Context.defs)
  def merge(a: Expr, b: Expr)(using order: Classes.Order): Classes =
    val cl = add(a).add(b)
    val ra = cl.find(a)
    val rb = cl.find(b)
    if ra == rb
    then cl
    else
      val (small, big) = if cl.members(ra).length <= cl.members(rb).length then (ra, rb) else (rb, ra)
      val (child, root) = if Ordering[Classes.Rank].lt(order.rank(small), order.rank(big)) then (big, small) else (small, big)
      val usesSmall = cl.uses.getOrElse(small, Nil)
      val usesBig = cl.uses.getOrElse(big, Nil)
      val members_ = cl.members(big) ++ cl.members(small)
      val merged = cl.copy(
        parent = cl.parent + (child -> root),
        merges = cl.merges + 1,
        retired = child :: cl.retired,
        members = cl.members - small - big + (root -> members_),
        uses = cl.uses - small - big + (root -> (usesBig ++ usesSmall)),
        clashed = cl.clashed || clashes(members_)
      )
      val pairs = for u <- usesSmall; v <- usesBig if merged.congruent(u, v) yield (u, v)
      pairs.foldLeft(merged)((cl, pair) => cl.merge(pair._1, pair._2))
