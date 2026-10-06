package cuvee.boogie

import easyparse.Token

type Typed = List[(List[String], Type)]

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
case class Array(index: Type, value: Type) extends Type

object Sort extends ((String, List[Type]) => Type)
object Array extends ((Type, Type) => Type)

case class Access(index: Expr, value: Option[Expr])
object Access extends ((Expr, Option[Expr]) => Access)

case class Num(value: String) extends Expr
case class Dec(value: String) extends Expr
case class Str(value: String) extends Expr
case class Butlast(arg: Expr) extends Expr
case class App(fun: String, args: List[Expr]) extends Expr
case class Inner(base: Expr, access: List[Access]) extends Expr
case class Ite(test: Expr, left: Expr, right: Expr) extends Expr
case class Ex(bound: Typed, triggers: List[List[Expr]], body: Expr) extends Expr
case class All(bound: Typed, triggers: List[List[Expr]], body: Expr) extends Expr

object Num extends (String => Expr)
object Dec extends (String => Expr)
object Str extends (String => Expr)
object Butlast extends (Expr => Expr)
object App extends ((String, List[Expr]) => Expr)
object Inner extends ((Expr, List[Access]) => Expr)
object True extends App("true", Nil)

case class Combinator(kind: String, init: Option[Expr], deps: List[Expr], bound: List[String], update: List[(Expr, Expr)]) extends Expr
object Combinator extends ((String, Option[Expr], List[Expr], List[String], List[(Expr, Expr)]) => Expr)
object Ite extends ((Expr, Expr, Expr) => Expr)
object Ex extends ((Typed, List[List[Expr]], Expr) => Expr)
object All extends ((Typed, List[List[Expr]], Expr) => Expr)

case class Lhs(name: String, indices: List[Expr])
object Lhs extends ((String, List[Expr]) => Lhs)

case object Skip extends Prog
case object Break extends Prog
case object Continue extends Prog
case object Return extends Prog
case class Assume(phi: Expr) extends Prog
case class Assert(phi: Expr) extends Prog
case class Assign(lhs: List[Lhs], rhs: List[Expr]) extends Prog
case class Havoc(vars: List[String]) extends Prog
case class Call(lhs: List[String], proc: String, args: List[Expr]) extends Prog
case class Local(vars: Typed)
case class Block(locals: List[Local], progs: List[Prog]) extends Prog
case class If(test: Option[Expr], left: Prog, right: Prog) extends Prog
case class While(test: Option[Expr], specs: List[Spec], body: Prog) extends Prog

object Assume extends (Expr => Prog)
object Assert extends (Expr => Prog)
object Assign extends ((List[Lhs], List[Expr]) => Prog)
object Havoc extends (List[String] => Prog)
object Call extends ((List[String], String, List[Expr]) => Prog)
object Local extends (Typed => Local)
object Block extends ((List[Local], List[Prog]) => Prog)
object If extends ((Option[Expr], Prog, Prog) => Prog)
object While extends ((Option[Expr], List[Spec], Prog) => Prog)

sealed trait Spec
case class Requires(phi: Expr) extends Spec
case class Ensures(phi: Expr) extends Spec
case class Invariant(phi: Expr) extends Spec
case class Modifies(vars: List[String]) extends Spec
case class Decreases(exprs: List[Expr]) extends Spec

object Requires extends (Expr => Spec)
object Ensures extends (Expr => Spec)
object Invariant extends (Expr => Spec)
object Modifies extends (List[String] => Spec)
object Decreases extends (List[Expr] => Spec)

case class Attr(name: String, args: List[Expr])
object Attr extends ((String, List[Expr]) => Attr)

case class Axiom(params: List[String], attrs: List[Attr], phi: Expr) extends Cmd
case class Lemma(params: List[String], attrs: List[Attr], phi: Expr) extends Cmd
case class SortDef(attrs: List[Attr], name: String, params: List[String], alias: Option[Type]) extends Cmd
case class DataDef(attrs: List[Attr], datas: List[Data]) extends Cmd
case class Data(name: String, params: List[String], constrs: List[Constr])
case class ConstDef(attrs: List[Attr], consts: Typed) extends Cmd
case class VarDef(attrs: List[Attr], vars: Typed) extends Cmd

case class FunDef(
    attrs: List[Attr],
    name: String,
    params: List[String],
    formals: Typed,
    typ: Type,
    body: Option[Expr]
) extends Cmd

case class ProcDef(
    attrs: List[Attr],
    name: String,
    params: List[String],
    formals: Typed,
    rets: Typed,
    specs: List[Spec],
    body: Option[Prog]
) extends Cmd

object Axiom extends ((List[String], List[Attr], Expr) => Cmd)
object Lemma extends ((List[String], List[Attr], Expr) => Cmd)
object SortDef extends ((List[Attr], String, List[String], Option[Type]) => Cmd)
object DataDef extends ((List[Attr], List[Data]) => Cmd)
object Data extends ((String, List[String], List[Constr]) => Data)

case class Sel(name: String, typ: Type)
case class Constr(name: String, sels: List[Sel])
object Sel extends ((String, Type) => Sel)
object Constr extends ((String, List[Sel]) => Constr)
object ConstDef extends ((List[Attr], Typed) => Cmd)
object VarDef extends ((List[Attr], Typed) => Cmd)
object FunDef extends ((List[Attr], String, List[String], Typed, Type, Option[Expr]) => Cmd)

object ProcDef
    extends (
        (
            List[Attr],
            String,
            List[String],
            Typed,
            Typed,
            (List[Spec], Option[Prog])
        ) => Cmd
    ):
  def apply(
      attrs: List[Attr],
      name: String,
      params: List[String],
      formals: Typed,
      rets: Typed,
      contract: (List[Spec], Option[Prog])
  ): Cmd =
    val (specs, body) = contract
    ProcDef(attrs, name, params, formals, rets, specs, body)
