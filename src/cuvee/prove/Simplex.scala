package cuvee.prove

import util.Rational
import cuvee.core._

// a linear constraint 0 <= poly, or 0 < poly if strict, over the atoms of a normalized polynomial, whose monomials are
// linear in the atoms (monomials of higher degree are atoms of their own, see Linear.atom)
case class Constraint(poly: Poly, strict: Boolean):
  def atoms: Set[Expr] =
    poly.monos.flatMap(_.atoms.map(_._1)).toSet

  // the truth value of a constraint without atoms
  def holds: Option[Boolean] =
    if poly.monos.nonEmpty
    then None
    else if strict
    then Some(poly.const.isPositive)
    else Some(!poly.const.isNegative)

object Constraint:
  // left <= right and left < right
  def le(left: Poly, right: Poly) =
    Constraint((right - left).normalize, strict = false)

  def lt(left: Poly, right: Poly) =
    Constraint((right - left).normalize, strict = true)

// a rational c + d·δ with an infinitesimal δ > 0, by which strict bounds are expressed as non-strict ones (Dutertre
// and de Moura, A Fast Linear-Arithmetic Solver for DPLL(T), 2006)
case class Delta(c: Rational, d: Rational):
  def +(that: Delta) = Delta(c + that.c, d + that.d)
  def -(that: Delta) = Delta(c - that.c, d - that.d)
  def *(r: Rational) = Delta(c * r, d * r)
  def unary_- = Delta(-c, -d)

  def <(that: Delta): Boolean =
    c < that.c || (c == that.c && d < that.d)

  def <=(that: Delta): Boolean =
    this < that || this == that

object Delta:
  val zero = Delta(Rational(0), Rational(0))

// the general simplex over the rationals for the satisfiability of a conjunction of linear constraints, which is
// complete over the rationals: each distinct linear part Σ aᵢ xᵢ of the constraints is a slack variable with the
// bounds that the constraints give it, the atoms are the non-basic variables initially, and check pivots by Bland's
// rule until all basic variables are within their bounds (satisfiable) or some basic variable can not be fixed
// (unsatisfiable); strict bounds use Delta
object Simplex:
  // the linear part of a constraint with its leading coefficient positive, and the sign flipped if it was negated
  def linear(poly: Poly): (Poly, Boolean) =
    val lin = Poly(Rational(0), poly.monos)
    if lin.monos.headOption.exists(_.factor.isNegative) then (-lin, true) else (lin, false)

  def satisfiable(constraints: List[Constraint]): Boolean =
    constraints.foldLeft(Tableau.empty)(_.add(_)).sat

// the state of the simplex after a check, persistent: a constraint is added to the solved tableau of its context and
// pivots from there, so that the contexts that extend one another, and the checks of Context.implied, which add one
// constraint each, share the work; variables are indices, the atoms (monomials without their factors, such that
// products of atoms and powers are variables of their own, about which nothing is known) and the slacks, one per
// distinct linear part; `rows` maps the basic variables to their rows over the non-basic ones; the non-basic
// variables satisfy their bounds throughout, since a basic variable leaves the basis at the bound it violated
case class Tableau(
    atoms: Map[List[(Expr, BigInt)], Int],
    slacks: Map[Poly, Int],
    lower: Map[Int, Delta],
    upper: Map[Int, Delta],
    value: Map[Int, Delta],
    rows: Map[Int, Map[Int, Rational]],
    sat: Boolean):

  def size = atoms.size + slacks.size

  // 0 <= c + lin is lin >= -c (lower bound), and lin <= c if the linear part was negated (upper bound); strict bounds
  // are offset by δ; a constraint without atoms holds or contradicts on its own
  def add(con: Constraint): Tableau =
    con.holds match
      case _ if !sat     => this
      case Some(true)    => this
      case Some(false)   => copy(sat = false)
      case None          =>
        val (lin, negated) = Simplex.linear(con.poly)
        val delta = if con.strict then Rational(1) else Rational(0)
        val tableau = withSlack(lin)
        val s = tableau.slacks(lin)
        if !negated
        then
          val bound = Delta(-con.poly.const, delta)
          if tableau.lower.get(s).exists(bound <= _) then tableau else tableau.bounded(s, Some(bound), None)
        else
          val bound = Delta(con.poly.const, -delta)
          if tableau.upper.get(s).exists(_ <= bound) then tableau else tableau.bounded(s, None, Some(bound))

  // the slack of the linear part `lin`, with fresh non-basic atoms of value 0, and its row over the non-basic
  // variables, where the atoms that are basic are replaced by their rows
  def withSlack(lin: Poly): Tableau =
    if slacks.contains(lin)
    then this
    else
      val fresh = lin.monos.map(_.atoms).distinct.filterNot(atoms.contains)
      val atoms_ = atoms ++ fresh.zipWithIndex.map((key, i) => key -> (size + i))
      val value_ = value ++ fresh.indices.map(i => (size + i) -> Delta.zero)
      val row = lin.monos.foldLeft(Map[Int, Rational]()): (row, mono) =>
        val y = atoms_(mono.atoms)
        rows.get(y) match
          case Some(r) => r.foldLeft(row) { case (row, (z, b)) => Tableau.plus(row, z, mono.factor * b) }
          case None    => Tableau.plus(row, y, mono.factor)
      val s = size + fresh.length
      val v = row.foldLeft(Delta.zero) { case (acc, (y, a)) => acc + value_(y) * a }
      copy(atoms = atoms_, slacks = slacks + (lin -> s), value = value_ + (s -> v), rows = rows + (s -> row))

  // the tightened bounds of `s`, a conflict if the lower one exceeds the upper one; a non-basic `s` outside the bound
  // moves onto it, and the basic variables of the rows that contain it follow; then the check from this state
  def bounded(s: Int, lo: Option[Delta], hi: Option[Delta]): Tableau =
    val lower_ = lo.map(b => lower + (s -> b)).getOrElse(lower)
    val upper_ = hi.map(b => upper + (s -> b)).getOrElse(upper)
    if lower_.get(s).zip(upper_.get(s)).exists((l, h) => h < l)
    then copy(lower = lower_, upper = upper_, sat = false)
    else
      val target =
        if rows.contains(s) then None
        else lo.filter(value(s) < _).orElse(hi.filter(_ < value(s)))
      val value_ =
        target match
          case None    => value
          case Some(b) =>
            val d = b - value(s)
            rows.foldLeft(value + (s -> b)) { case (value, (x, row)) =>
              row.get(s).map(a => value + (x -> (value(x) + d * a))).getOrElse(value)
            }
      copy(lower = lower_, upper = upper_, value = value_).check()

  // pivots by Bland's rule on copies of the maps, until no basic variable violates its bounds (satisfiable) or one can
  // not be fixed (unsatisfiable)
  def check(): Tableau =
    val value = scala.collection.mutable.Map.from(this.value)
    val tableau = scala.collection.mutable.Map.from(rows.view.mapValues(scala.collection.mutable.Map.from(_)))

    // the value of a basic variable from the values of the non-basic ones
    def recompute(x: Int): Unit =
      value(x) = tableau(x).foldLeft(Delta.zero) { case (acc, (y, a)) => acc + value(y) * a }

    // the basic variable x leaves the basis, the non-basic y enters: x = ... + a y + ... is solved for y and substituted
    def pivot(x: Int, y: Int): Unit =
      val row = tableau.remove(x).get
      val a = row(y)
      val rowy = scala.collection.mutable.Map[Int, Rational]()
      for (z, b) <- row if z != y do rowy(z) = -b / a
      rowy(x) = Rational(1) / a
      for (z, r) <- tableau if r.contains(y)
      do
        val c = r.remove(y).get
        for (w, b) <- rowy
        do
          val b_ = r.getOrElse(w, Rational(0)) + c * b
          if b_.isZero then r.remove(w) else r(w) = b_
      tableau(y) = rowy

    def violated(x: Int): Boolean =
      lower.get(x).exists(value(x) < _) || upper.get(x).exists(_ < value(x))

    // x is basic and violates a bound: a non-basic variable y of its row that can move x towards the bound, pivoted
    // and set such that x takes the bound; Bland's rule chooses the smallest indices, which terminates
    var sat = true
    var done = false
    while !done do
      tableau.keys.filter(violated).toList.sorted match
        case Nil =>
          done = true

        case x :: _ =>
          val row = tableau(x)
          val toLower = lower.get(x).exists(value(x) < _)
          val target = if toLower then lower(x) else upper(x)
          val candidates =
            for
              (y, a) <- row.toList.sortBy(_._1)
              // increase x: y with positive coefficient may increase (below upper), negative may decrease (above lower)
              ok =
                if toLower
                then (a.isPositive && upper.get(y).forall(value(y) < _)) || (a.isNegative && lower.get(y).forall(_ < value(y)))
                else (a.isPositive && lower.get(y).forall(_ < value(y))) || (a.isNegative && upper.get(y).forall(value(y) < _))
              if ok
            yield y
          candidates match
            case Nil =>
              done = true
              sat = false

            // x takes its bound and y moves accordingly, then y enters the basis in place of x, and the values of
            // the basic variables follow from the non-basic ones, among them now x
            case y :: _ =>
              val a = row(y)
              val theta = (target - value(x)) * (Rational(1) / a)
              value(x) = target
              value(y) = value(y) + theta
              pivot(x, y)
              for z <- tableau.keys do recompute(z)

    copy(value = value.toMap, rows = tableau.view.mapValues(_.toMap).toMap, sat = sat)

object Tableau:
  val empty = Tableau(Map(), Map(), Map(), Map(), Map(), Map(), sat = true)

  // the row with b added to the coefficient of z, without zero coefficients
  def plus(row: Map[Int, Rational], z: Int, b: Rational): Map[Int, Rational] =
    val c = row.getOrElse(z, Rational(0)) + b
    if c.isZero then row - z else row + (z -> c)
