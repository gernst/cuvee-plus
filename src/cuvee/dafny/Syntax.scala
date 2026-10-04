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
// tuple types (A, B, ...) with at least two components
case class Product(args: List[Type]) extends Type

object Sort extends ((String, List[Type]) => Type)
object Product extends (List[Type] => Type)

object True extends App("true", Nil, Nil)

sealed trait Access
case class Array(index: Expr, value: Option[Expr]) extends Access
// slices of sequences s[i..j], where both bounds are optional
case class Slice(from: Option[Expr], to: Option[Expr]) extends Access
case class Member(fun: String, args: List[Expr]) extends Access

object Array extends ((Expr, Option[Expr]) => Access)
object Slice extends ((Option[Expr], Option[Expr]) => Access)
object Member extends ((String, List[Expr]) => Access)

case class Num(value: String) extends Expr
// decimal literals of type real, e.g. 1.5
case class Dec(value: String) extends Expr
case class Str(value: String) extends Expr
case class Tuple(args: List[Expr]) extends Expr
// sequence literals [a, b, c] and the length |s| of a sequence
case class SeqLit(args: List[Expr]) extends Expr
case class Len(arg: Expr) extends Expr
// set literals {a, b, c} and multiset literals multiset{a, b, c}
case class SetLit(args: List[Expr]) extends Expr
case class BagLit(args: List[Expr]) extends Expr
// all but the last element ⌊X⌋ of a trace
case class Butlast(arg: Expr) extends Expr
// the derivative (x, y :: e)' of e with respect to x and y
case class Diff(xs: List[String], expr: Expr) extends Expr
case class App(fun: String, args: List[Expr], access: List[Access]) extends Expr
case class Ite(test: Expr, left: Expr, right: Expr) extends Expr
// type annotations e as T, testers e.C? are members whose name ends with ?
case class As(expr: Expr, typ: Type) extends Expr
// indexing and slices of expressions other than names and calls, e.g. (if b then s else t)[0]
case class Access_(base: Expr, access: List[Access]) extends Expr
case class Ex(bound: List[(String, Type)], body: Expr) extends Expr
case class All(bound: List[(String, Type)], body: Expr) extends Expr
case class Let(bound: List[(String, Type)], args: List[Expr], body: Expr) extends Expr

object Num extends (String => Expr)
object Dec extends (String => Expr)
object Str extends (String => Expr)
object Tuple extends (List[Expr] => Expr)
object SeqLit extends (List[Expr] => Expr)
object Len extends (Expr => Expr)
object SetLit extends (List[Expr] => Expr)
object BagLit extends (List[Expr] => Expr)
object Butlast extends (Expr => Expr)
object Diff extends ((List[String], Expr) => Expr)
object App extends ((String, List[Expr], List[Access]) => Expr)

// the combinators of trace equation systems, trace(init, for deps do acc, bound => update),
// map(for deps yield bound => update), and all(for deps check bound => body),
// where the update are guarded cases if guard then result, ..., and the body of all is a single case
case class Combinator(kind: String, init: Option[Expr], deps: List[Expr], bound: List[String], update: List[(Expr, Expr)]) extends Expr
object Ite extends ((Expr, Expr, Expr) => Expr)
object As extends ((Expr, Type) => Expr)
object Access_ extends ((Expr, List[Access]) => Expr)
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
// the test is None for nondeterministic iterations, while * { body }
case class While(test: Option[Expr], invs: List[Expr], dec: List[List[Expr]], body: Prog) extends Prog
// differential equations x', y' == e, f && dom invariant ..., the variables are without prime
case class Ode(xs: List[String], rhs: List[Expr], dom: Option[Expr], invs: List[Expr]) extends Prog

// local variable declarations with optional initial values, var x: int, y: int := 1, 2;
case class Local(vars: List[(String, Type)], init: Option[List[Expr]])
object Local extends ((List[(String, Type)], Option[List[Expr]]) => Local)

object Assume extends (Expr => Prog)
object Assert extends (Expr => Prog)
object Assign extends ((List[String], List[Expr]) => Prog)
object Block extends ((List[Local], List[Prog]) => Prog)
object If extends ((Option[Expr], Prog, Prog) => Prog)
object While extends ((Option[Expr], List[Expr], List[List[Expr]], Prog) => Prog)
object Ode extends ((List[String], List[Expr], Option[Expr], List[Expr]) => Prog)

// parallel composition of calls, parallel { p(a); x := q(b); }
case class Par(calls: List[Prog]) extends Prog

object Par extends (List[Prog] => Prog)

case class Sel(name: String, typ: Type)
case class Constr(name: String, sels: List[Sel])

object Sel extends ((String, Type) => Sel)
object Constr extends ((String, List[Sel]) => Constr)

// axioms and lemmas with attributes, e.g. axiom {:rw} e for rewrite rules
case class Axiom(attrs: List[String], phi: Expr) extends Cmd
case class Lemma(attrs: List[String], phi: Expr) extends Cmd
// formulas to be proved, which are not assumed afterwards, unlike lemmas, not Dafny
case class Goal(attrs: List[String], phi: Expr) extends Cmd
// check-sat, which is not Dafny
case object Check extends Cmd
// global variables, var x: int; which are not Dafny
case class VarDef(vars: List[(String, Type)]) extends Cmd
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

// methods, with assumption-commitment contracts for parallel composition
case class MethodDef(
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

object Axiom extends ((List[String], Expr) => Cmd)
object Lemma extends ((List[String], Expr) => Cmd)
object Goal extends ((List[String], Expr) => Cmd)
object VarDef extends (List[(String, Type)] => Cmd)
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
            List[Expr],
            List[Expr],
            List[List[Expr]],
            Option[Prog]
        ) => Cmd
    )
