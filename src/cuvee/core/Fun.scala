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

case class Fun(name: Name, params: List[Param], formals: List[Var], res: Type):
  def args = formals.types
  def arity = formals.length
  def sig = Sig(name, args.sig)

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

  val not = Fun("not", Nil, formals(bool), bool)
  val imp = Fun("=>", Nil, formals(bool, bool), bool)
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
