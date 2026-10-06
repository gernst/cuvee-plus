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

  // finite sets as in cvc5, where set.empty needs its type, (as set.empty (Set a)), and member takes the element first
  object set:
    val empty = Fun("set.empty", List(a), Nil, Sort.set(a))
    val singleton = Fun("set.singleton", List(a), formals(a), Sort.set(a))
    val union = Fun("set.union", List(a), formals(Sort.set(a), Sort.set(a)), Sort.set(a))
    val inter = Fun("set.inter", List(a), formals(Sort.set(a), Sort.set(a)), Sort.set(a))
    val minus = Fun("set.minus", List(a), formals(Sort.set(a), Sort.set(a)), Sort.set(a))
    val member = Fun("set.member", List(a), formals(a, Sort.set(a)), bool)
    val subset = Fun("set.subset", List(a), formals(Sort.set(a), Sort.set(a)), bool)
    val card = Fun("set.card", List(a), formals(Sort.set(a)), Sort.int)

    val all = List(empty, singleton, union, inter, minus, member, subset, card)

  // finite multisets (bags) as in cvc5, where bag(x, n) holds x with multiplicity n,
  // the union adds multiplicities, the intersection takes the minimum, and the difference subtracts them
  object bag:
    val empty = Fun("bag.empty", List(a), Nil, Sort.bag(a))
    val make = Fun("bag", List(a), formals(a, Sort.int), Sort.bag(a))
    val union = Fun("bag.union_disjoint", List(a), formals(Sort.bag(a), Sort.bag(a)), Sort.bag(a))
    val inter = Fun("bag.inter_min", List(a), formals(Sort.bag(a), Sort.bag(a)), Sort.bag(a))
    val minus = Fun("bag.difference_subtract", List(a), formals(Sort.bag(a), Sort.bag(a)), Sort.bag(a))
    val count = Fun("bag.count", List(a), formals(a, Sort.bag(a)), Sort.int)
    val subbag = Fun("bag.subbag", List(a), formals(Sort.bag(a), Sort.bag(a)), bool)
    val card = Fun("bag.card", List(a), formals(Sort.bag(a)), Sort.int)

    val all = List(empty, make, union, inter, minus, count, subbag, card)

  // finite maps, named like the sets of cvc5, which however has no such theory, where map.empty needs its type,
  // map.get is unspecified outside of the keys, map.update(m, n) overwrites m by n, and map.minus removes keys
  object map:
    val empty = Fun("map.empty", List(a, b), Nil, Sort.map(a, b))
    val singleton = Fun("map.singleton", List(a, b), formals(a, b), Sort.map(a, b))
    val card = Fun("map.card", List(a, b), formals(Sort.map(a, b)), Sort.int)
    val member = Fun("map.member", List(a, b), formals(a, Sort.map(a, b)), bool)
    val keys = Fun("map.keys", List(a, b), formals(Sort.map(a, b)), Sort.set(a))
    val values = Fun("map.values", List(a, b), formals(Sort.map(a, b)), Sort.set(b))
    val subset = Fun("map.subset", List(a, b), formals(Sort.map(a, b), Sort.map(a, b)), bool)
    val get = Fun("map.get", List(a, b), formals(Sort.map(a, b), a), b)
    val update = Fun("map.update", List(a, b), formals(Sort.map(a, b), Sort.map(a, b)), Sort.map(a, b))
    val minus = Fun("map.minus", List(a, b), formals(Sort.map(a, b), Sort.set(a)), Sort.map(a, b))

    val all = List(empty, singleton, card, member, keys, values, subset, get, update, minus)

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
