package cuvee.core

import util.Name
import scala.annotation.targetName

case class Sig(name: Name, sorts: List[Option[Sig]]):
  infix def <=(that: Sig): Boolean =
    val Sig(name_, sorts_) = that
    if name != name_
    then false
    else if sorts.length != sorts_.length
    then false
    else
      (sorts zip sorts_).forall:
        case (_, None)               => true
        case (Some(sig), Some(sig_)) => sig <= sig_
        case _                       => false

// functions are equal if their names and signatures are, regardless of the names of the formal parameters,
// e.g. the declarations of built-in functions in the preludes and the values below
case class Fun(name: Name, params: List[Param], formals: List[Var], res: Type):
  def args = formals.types
  def arity = formals.length
  def sig = Sig(name, args.sig)

  override def equals(that: Any) =
    that match
      case Fun(name_, params_, formals_, res_) =>
        name == name_ && params == params_ && args == formals_.types && res == res_

      case _ =>
        false

  override def hashCode =
    (name, params, args, res).hashCode

object Fun:
  import Param.a
  import Param.b
  import Sort.bool

  // formal parameters are named x$0, x$1, ... as for functions declared in SMT-LIB
  def formals(types: Type*) =
    Expr.vars("x", types.toList)

  val true_ = Fun("true", Nil, Nil, bool)
  val false_ = Fun("false", Nil, Nil, bool)

  val eq_ = Fun("=", List(a), formals(a, a), bool)
  val ite = Fun("ite", List(a), formals(bool, a, a), a)

  val select = Fun("select", List(a, b), formals(Sort.array(a, b), a), b)
  val store = Fun("store", List(a, b), formals(Sort.array(a, b), a, b), Sort.array(a, b))
  val const = Fun("const", List(a, b), formals(b), Sort.array(a, b))

  // sequences as in cvc5, where seq.empty needs its type, (as seq.empty (Seq a)),
  // seq.extract takes an offset and a length, and seq.update and seq.contains take a subsequence
  object seq:
    val empty = Fun("seq.empty", List(a), Nil, Sort.seq(a))
    val unit = Fun("seq.unit", List(a), formals(a), Sort.seq(a))
    val concat = Fun("seq.++", List(a), formals(Sort.seq(a), Sort.seq(a)), Sort.seq(a))
    val len = Fun("seq.len", List(a), formals(Sort.seq(a)), Sort.int)
    val nth = Fun("seq.nth", List(a), formals(Sort.seq(a), Sort.int), a)
    val update = Fun("seq.update", List(a), formals(Sort.seq(a), Sort.int, Sort.seq(a)), Sort.seq(a))
    val extract = Fun("seq.extract", List(a), formals(Sort.seq(a), Sort.int, Sort.int), Sort.seq(a))
    val contains = Fun("seq.contains", List(a), formals(Sort.seq(a), Sort.seq(a)), bool)
    val prefixof = Fun("seq.prefixof", List(a), formals(Sort.seq(a), Sort.seq(a)), bool)

    val all = List(empty, unit, concat, len, nth, update, extract, contains, prefixof)

  // the functions on traces and sequences of trace equation systems: counter(i, c, n) is the trace i, i + c, ..., i + n c,
  // current the last element of a trace, butlast (written ⌊X⌋) all but the last element, steps the number of iterations,
  // length the length of a sequence, nth and earlier the elements of traces and sequences
  object trace:
    val counter = Fun("counter", Nil, formals(Sort.int, Sort.int, Sort.int), Sort.trace(Sort.int))
    val current = Fun("current", List(a), formals(Sort.trace(a)), a)
    val butlast = Fun("butlast", List(a), formals(Sort.trace(a)), Sort.seq(a))
    val steps = Fun("steps", List(a), formals(Sort.trace(a)), Sort.int)
    val length = Fun("length", List(a), formals(Sort.seq(a)), Sort.int)
    val nth = Fun("nth", List(a), formals(Sort.int, Sort.trace(a)), a)
    val earlier = Fun("earlier", List(a), formals(Sort.int, Sort.seq(a)), a)

    val all = List(counter, current, butlast, steps, length, nth, earlier)

  val not = Fun("not", Nil, formals(bool), bool)
  val imp = Fun("=>", Nil, formals(bool, bool), bool)
  // equivalence, which SMT-LIB writes as = on Bool, declared by the preludes of all frontends
  val eqv = Fun("<=>", Nil, formals(bool, bool), bool)
  val and = Fun("and", Nil, formals(bool, bool), bool)
  val or = Fun("or", Nil, formals(bool, bool), bool)

  // arithmetic and comparison, which SMT-LIB overloads for Int and Real
  object int:
    val uminus = Fun("-", Nil, formals(Sort.int), Sort.int)
    val plus = Fun("+", Nil, formals(Sort.int, Sort.int), Sort.int)
    val minus = Fun("-", Nil, formals(Sort.int, Sort.int), Sort.int)
    val times = Fun("*", Nil, formals(Sort.int, Sort.int), Sort.int)
    val div = Fun("div", Nil, formals(Sort.int, Sort.int), Sort.int)
    val mod = Fun("mod", Nil, formals(Sort.int, Sort.int), Sort.int)

    val lt = Fun("<", Nil, formals(Sort.int, Sort.int), bool)
    val le = Fun("<=", Nil, formals(Sort.int, Sort.int), bool)
    val gt = Fun(">", Nil, formals(Sort.int, Sort.int), bool)
    val ge = Fun(">=", Nil, formals(Sort.int, Sort.int), bool)

    val all = List(uminus, plus, minus, times, div, mod, lt, le, gt, ge)

  object real:
    val uminus = Fun("-", Nil, formals(Sort.real), Sort.real)
    val plus = Fun("+", Nil, formals(Sort.real, Sort.real), Sort.real)
    val minus = Fun("-", Nil, formals(Sort.real, Sort.real), Sort.real)
    val times = Fun("*", Nil, formals(Sort.real, Sort.real), Sort.real)
    val div = Fun("/", Nil, formals(Sort.real, Sort.real), Sort.real)

    val lt = Fun("<", Nil, formals(Sort.real, Sort.real), bool)
    val le = Fun("<=", Nil, formals(Sort.real, Sort.real), bool)
    val gt = Fun(">", Nil, formals(Sort.real, Sort.real), bool)
    val ge = Fun(">=", Nil, formals(Sort.real, Sort.real), bool)

    val all = List(uminus, plus, minus, times, div, lt, le, gt, ge)
