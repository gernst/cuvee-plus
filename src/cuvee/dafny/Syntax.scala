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
// a function type A -> R, whose argument is a product (A₁, ..., Aₙ) for several arguments
case class Arrow(arg: Type, res: Type) extends Type

object Sort extends ((String, List[Type]) => Type)
object Product extends (List[Type] => Type)
object Arrow extends ((Type, Type) => Type)

object True extends App("true", Nil)

sealed trait Access
case class Array(index: Option[Expr], suffix: Option[Suffix]) extends Access
case class Member(fun: String, args: List[Expr]) extends Access
case class As(typ: Type) extends Access

object Array extends ((Option[Expr], Option[Suffix]) => Access)

sealed trait Suffix
case class Store(value: Expr) extends Suffix
case class Upto(to: Option[Expr]) extends Suffix

object Store extends (Expr => Suffix)
object Upto extends (Option[Expr] => Suffix)
object Member extends ((String, List[Expr]) => Access)
object As extends (Type => Access)

case class Num(value: String) extends Expr
case class Dec(value: String) extends Expr
case class Str(value: String) extends Expr
case class Tuple(args: List[Expr]) extends Expr
case class SeqLit(args: List[Expr]) extends Expr
case class Len(arg: Expr) extends Expr
case class SetLit(args: List[Expr]) extends Expr
case class BagLit(args: List[Expr]) extends Expr
case class MapLit(args: List[(Expr, Expr)]) extends Expr
case class Butlast(arg: Expr) extends Expr
case class Diff(xs: List[String], expr: Expr) extends Expr
case class App(fun: String, args: List[Expr]) extends Expr
case class Ite(test: Expr, left: Expr, right: Expr) extends Expr
case class Match(arg: Expr, cases: List[(Expr, Expr)]) extends Expr
case class Inner(base: Expr, access: List[Access]) extends Expr
case class Ex(bound: List[(String, Type)], body: Expr) extends Expr
case class All(bound: List[(String, Type)], body: Expr) extends Expr
// the variables of lambdas are always annotated with their types
case class Lam(bound: List[(String, Type)], body: Expr) extends Expr
case class Let(bound: List[(String, Type)], args: List[Expr], body: Expr) extends Expr

object Num extends (String => Expr)
object Dec extends (String => Expr)
object Str extends (String => Expr)
object Tuple extends (List[Expr] => Expr)
object SeqLit extends (List[Expr] => Expr)
object Len extends (Expr => Expr)
object SetLit extends (List[Expr] => Expr)
object BagLit extends (List[Expr] => Expr)
object MapLit extends (List[(Expr, Expr)] => Expr)
object Butlast extends (Expr => Expr)
object Diff extends ((List[String], Expr) => Expr)
object App extends ((String, List[Expr]) => Expr)

case class Combinator(kind: String, init: Option[Expr], deps: List[Expr], bound: List[String], update: List[(Expr, Expr)]) extends Expr
object Combinator extends ((String, Option[Expr], List[Expr], List[String], List[(Expr, Expr)]) => Expr)
object Ite extends ((Expr, Expr, Expr) => Expr)
object Match extends ((Expr, List[(Expr, Expr)]) => Expr)
object Inner extends ((Expr, List[Access]) => Expr)
object Ex extends ((List[(String, Type)], Expr) => Expr)
object All extends ((List[(String, Type)], Expr) => Expr)
object Lam extends ((List[(String, Type)], Expr) => Expr)
object Let extends ((List[(String, Type)], List[Expr], Expr) => Expr)

case object Break extends Prog
case object Continue extends Prog
case object Return extends Prog
case class Assume(phi: Expr) extends Prog
case class Assert(phi: Expr) extends Prog
// not Dafny, arbitrary values of the variables, as printed for Spec(xs, true, true)
case class Havoc(xs: List[String]) extends Prog
// the left-hand sides of assignments are variables or their elements, a[i][j] := v (see Parser.update)
case class Lhs(name: String, indices: List[Expr])
case class Assign(lhs: List[Lhs], rhs: List[Expr]) extends Prog
case object Skip extends Prog
case class Block(locals: List[Local], progs: List[Prog]) extends Prog
case class If(test: Option[Expr], left: Prog, right: Prog) extends Prog
case class While(test: Option[Expr], mod: List[List[String]], invs: List[Expr], dec: List[List[Expr]], body: Prog) extends Prog
case class Ode(time: String, xs: List[String], rhs: List[Expr], dom: Option[Expr], invs: List[Expr]) extends Prog

case class Local(vars: List[(String, Type)], init: Option[List[Expr]])
object Local extends ((List[(String, Type)], Option[List[Expr]]) => Local)

object Assume extends (Expr => Prog)
object Assert extends (Expr => Prog)
object Havoc extends (List[String] => Prog)
object Lhs extends ((String, List[Expr]) => Lhs)
object Assign extends ((List[Lhs], List[Expr]) => Prog)
object Block extends ((List[Local], List[Prog]) => Prog)
object If extends ((Option[Expr], Prog, Prog) => Prog)
object While extends ((Option[Expr], List[List[String]], List[Expr], List[List[Expr]], Prog) => Prog)
object Ode extends ((String, List[String], List[Expr], Option[Expr], List[Expr]) => Prog)

case class Par(calls: List[Prog]) extends Prog

object Par extends (List[Prog] => Prog)

case class Sel(name: String, typ: Type)
case class Constr(name: String, sels: List[Sel])

object Sel extends ((String, Type) => Sel)
object Constr extends ((String, List[Sel]) => Constr)

case class Axiom(params: List[String], attrs: List[String], phi: Expr) extends Cmd
case class Lemma(params: List[String], attrs: List[String], phi: Expr) extends Cmd
case class Goal(params: List[String], attrs: List[String], phi: Expr) extends Cmd
case object Check extends Cmd
// fuse term = ???, where term is the composition of two defined functions (see core.FuseFuns)
case class Fuse(attrs: List[String], term: Expr) extends Cmd
case class VarDef(vars: List[(String, Type)]) extends Cmd
case class SortDef(attrs: List[String], name: String, params: List[String], impl: Either[Option[Type], List[Cmd]]) extends Cmd
case class DataDef(attrs: List[String], name: String, params: List[String], constrs: List[Constr], impl: Option[List[Cmd]]) extends Cmd
case class DataDefs(datas: List[DataDef]) extends Cmd

case class FunDef(
    attrs: List[String],
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
    attrs: List[String],
    name: String,
    params: List[String],
    formals: List[(String, Type)],
    rets: Option[List[(String, Type)]],
    mod: List[List[String]],
    req: List[Expr],
    ens: List[Expr],
    assumes: List[Expr],
    commits: List[Expr],
    dec: List[List[Expr]],
    body: Option[Prog]
) extends Cmd

object Axiom extends ((List[String], List[String], Expr) => Cmd)
object Lemma extends ((List[String], List[String], Expr) => Cmd)
object Goal extends ((List[String], List[String], Expr) => Cmd)
object Fuse extends ((List[String], Expr) => Cmd)
object VarDef extends (List[(String, Type)] => Cmd)
object SortDef extends ((List[String], String, List[String], Either[Option[Type], List[Cmd]]) => Cmd)
object DataDef extends ((List[String], String, List[String], List[Constr], Option[List[Cmd]]) => DataDef)
object DataDefs extends (List[DataDef] => Cmd)
object FunDef extends ((List[String], String, List[String], List[(String, Type)], Type, List[Expr], List[Expr], List[List[Expr]], Option[Expr]) => Cmd)

object MethodDef
    extends (
        (
            List[String],
            String,
            List[String],
            List[(String, Type)],
            Option[List[(String, Type)]],
            List[List[String]],
            List[Expr],
            List[Expr],
            List[Expr],
            List[Expr],
            List[List[Expr]],
            Option[Prog]
        ) => Cmd
    )
