package cuvee.dafny

import easyparse.Token

object Syntax:
  import easyparse._

  def apply(name: String) =
    Token.Keyword(name)

  def apply(name: String, text: String) =
    Token.Value(name, text)

sealed trait Type
sealed trait Expr
sealed trait Prog
sealed trait Cmd

case class Sort(con: String, args: List[Type]) extends Type
case class Product(args: List[Type]) extends Type

object Sort extends ((String, List[Type]) => Type)

object True extends App("true", Nil, Nil)

sealed trait Access
case class Array(index: Expr, value: Option[Expr]) extends Access
case class Member(fun: String, args: List[Expr]) extends Access

object Array extends ((Expr, Option[Expr]) => Access)
object Member extends ((String, List[Expr]) => Access)

case class Num(value: String) extends Expr
case class Str(value: String) extends Expr
case class App(fun: String, args: List[Expr], access: List[Access]) extends Expr
case class Ite(test: Expr, left: Expr, right: Expr) extends Expr
case class Ex(bound: List[(String, Type)], body: Expr) extends Expr
case class All(bound: List[(String, Type)], body: Expr) extends Expr
case class Let(bound: List[(String, Type)], args: List[Expr], body: Expr) extends Expr

object Num extends (String => Expr)
object Str extends (String => Expr)
object App extends ((String, List[Expr], List[Access]) => Expr)
object Ite extends ((Expr, Expr, Expr) => Expr)
object Ex extends ((List[(String, Type)], Expr) => Expr)
object All extends ((List[(String, Type)], Expr) => Expr)
object Let extends ((List[(String, Type)], List[Expr], Expr) => Expr)

case object Skip extends Prog
case object Break extends Prog
case object Continue extends Prog
case object Return extends Prog
case class Assume(phi: Expr) extends Prog
case class Assert(phi: Expr) extends Prog
case class Assign(lhs: List[String], rhs: List[Expr]) extends Prog
case class Block(locals: List[Local], progs: List[Prog]) extends Prog
// the test is None for a nondeterministic choice, if * { left } else { right }
case class If(test: Option[Expr], left: Prog, right: Prog) extends Prog
case class While(test: Expr, invs: List[Expr], dec: List[List[Expr]], body: Prog) extends Prog

// local variable declarations with optional initial values, var x: int, y: int := 1, 2;
case class Local(vars: List[(String, Type)], init: Option[List[Expr]])
object Local extends ((List[(String, Type)], Option[List[Expr]]) => Local)

object Assume extends (Expr => Prog)
object Assert extends (Expr => Prog)
object Assign extends ((List[String], List[Expr]) => Prog)
object Block extends ((List[Local], List[Prog]) => Prog)
object If extends ((Option[Expr], Prog, Prog) => Prog)
object While extends ((Expr, List[Expr], List[List[Expr]], Prog) => Prog)

case class Sel(name: String, typ: Type)
case class Constr(name: String, sels: List[Sel])

object Sel extends ((String, Type) => Sel)
object Constr extends ((String, List[Sel]) => Constr)

case class Axiom(phi: Expr) extends Cmd
case class SortDef(name: String, params: List[String], impl: Either[Option[Type], List[Cmd]]) extends Cmd
case class DataDef(name: String, params: List[String], constrs: List[Constr], impl: Option[List[Cmd]]) extends Cmd

case class FunDef(
    name: String,
    params: List[String],
    formals: List[(String, Type)],
    typ: Type,
    req: List[Expr],
    ens: List[Expr],
    dec: List[List[Expr]],
    body: Option[Expr]
) extends Cmd

case class MethodDef(
    name: String,
    params: List[String],
    formals: List[(String, Type)],
    rets: Option[List[(String, Type)]],
    mod: List[List[String]],
    req: List[Expr],
    ens: List[Expr],
    dec: List[List[Expr]],
    body: Option[Prog]
) extends Cmd

object Axiom extends (Expr => Cmd)
object SortDef extends ((String, List[String], Either[Option[Type], List[Cmd]]) => Cmd)
object DataDef extends ((String, List[String], List[Constr], Option[List[Cmd]]) => Cmd)
object FunDef extends ((String, List[String], List[(String, Type)], Type, List[Expr], List[Expr], List[List[Expr]], Option[Expr]) => Cmd)

object MethodDef
    extends (
        (
            String,
            List[String],
            List[(String, Type)],
            Option[List[(String, Type)]],
            List[List[String]],
            List[Expr],
            List[Expr],
            List[List[Expr]],
            Option[Prog]
        ) => Cmd
    )
