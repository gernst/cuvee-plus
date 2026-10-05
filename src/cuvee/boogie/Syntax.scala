package cuvee.boogie

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

// user-defined sorts and type parameters, e.g. List int and a,
// and maps with a single index as SMT-LIB arrays, [int]bool
case class Sort(con: String, args: List[Type]) extends Type
case class Array(index: Type, value: Type) extends Type

object Sort extends ((String, List[Type]) => Type)
object Array extends ((Type, Type) => Type)

// map selection a[i] if value is None, otherwise update a[i := v]
case class Access(index: Expr, value: Option[Expr])
object Access extends ((Expr, Option[Expr]) => Access)

// variables and constants are applications without arguments,
// followed by map accesses, e.g. a[i][j := v]
case class Num(value: String) extends Expr
// decimal literals of type real, e.g. 1.5
case class Dec(value: String) extends Expr
case class Str(value: String) extends Expr
// all but the last element ⌊X⌋ of a trace
case class Butlast(arg: Expr) extends Expr
case class App(fun: String, args: List[Expr], access: List[Access]) extends Expr
case class Ite(test: Expr, left: Expr, right: Expr) extends Expr
// each trigger is a list of expressions, e.g. { f(x), g(x) }
case class Ex(bound: List[(String, Type)], triggers: List[List[Expr]], body: Expr) extends Expr
case class All(bound: List[(String, Type)], triggers: List[List[Expr]], body: Expr) extends Expr

object Num extends (String => Expr)
object Dec extends (String => Expr)
object Str extends (String => Expr)
object Butlast extends (Expr => Expr)
object App extends ((String, List[Expr], List[Access]) => Expr)

// the combinators of trace equation systems, trace(init, for deps do acc, bound => update),
// map(for deps yield bound => update), and all(for deps check bound => body),
// where the update are guarded cases if guard then result, ..., and the body of all is a single case
case class Combinator(kind: String, init: Option[Expr], deps: List[Expr], bound: List[String], update: List[(Expr, Expr)]) extends Expr
object Ite extends ((Expr, Expr, Expr) => Expr)
object Ex extends ((List[(String, Type)], List[List[Expr]], Expr) => Expr)
object All extends ((List[(String, Type)], List[List[Expr]], Expr) => Expr)

// the left-hand side of an assignment is a variable with indices, e.g. a[i][j] := v
case class Lhs(name: String, indices: List[Expr])
object Lhs extends ((String, List[Expr]) => Lhs)

case object Skip extends Prog
case object Break extends Prog
// not Boogie, the next iteration of the innermost loop
case object Continue extends Prog
case object Return extends Prog
case class Assume(phi: Expr) extends Prog
case class Assert(phi: Expr) extends Prog
case class Assign(lhs: List[Lhs], rhs: List[Expr]) extends Prog
case class Havoc(vars: List[String]) extends Prog
case class Call(lhs: List[String], proc: String, args: List[Expr]) extends Prog
// local variables are declared at the beginning of a block
case class Block(locals: List[(String, Type)], progs: List[Prog]) extends Prog
// the test is None for a nondeterministic choice, if (*) { left } else { right }
case class If(test: Option[Expr], left: Prog, right: Prog) extends Prog
// the test is None for nondeterministic iterations, while (*) { body }
case class While(test: Option[Expr], specs: List[Spec], body: Prog) extends Prog

object Assume extends (Expr => Prog)
object Assert extends (Expr => Prog)
object Assign extends ((List[Lhs], List[Expr]) => Prog)
object Havoc extends (List[String] => Prog)
object Call extends ((List[String], String, List[Expr]) => Prog)
object Block extends ((List[(String, Type)], List[Prog]) => Prog)
object If extends ((Option[Expr], Prog, Prog) => Prog)
object While extends ((Option[Expr], List[Spec], Prog) => Prog)

// the specification clauses of procedures and loops, in any order;
// modifies clauses of loops are an extension of Boogie
sealed trait Spec
case class Requires(phi: Expr) extends Spec
case class Ensures(phi: Expr) extends Spec
case class Invariant(phi: Expr) extends Spec
case class Modifies(vars: List[String]) extends Spec
// a lexicographic termination measure, not Boogie
case class Decreases(exprs: List[Expr]) extends Spec

object Requires extends (Expr => Spec)
object Ensures extends (Expr => Spec)
object Invariant extends (Expr => Spec)
object Modifies extends (List[String] => Spec)
object Decreases extends (List[Expr] => Spec)

// attributes of top-level commands, e.g. {:inline} and {:msg "text", x}
case class Attr(name: String, args: List[Expr])
object Attr extends ((String, List[Expr]) => Attr)

// several constants or global variables can be declared at once, e.g. var x, y: int, b: bool;
// with type parameters, axiom <a> {:rw} (forall x: a :: φ);
case class Axiom(params: List[String], attrs: List[Attr], phi: Expr) extends Cmd
// not part of Boogie, lemmas are proved and then assumed like axioms
case class Lemma(params: List[String], attrs: List[Attr], phi: Expr) extends Cmd
case class SortDef(attrs: List[Attr], name: String, params: List[String], alias: Option[Type]) extends Cmd
case class ConstDef(attrs: List[Attr], consts: List[(String, Type)]) extends Cmd
case class VarDef(attrs: List[Attr], vars: List[(String, Type)]) extends Cmd

case class FunDef(
    attrs: List[Attr],
    name: String,
    params: List[String],
    formals: List[(String, Type)],
    typ: Type,
    body: Option[Expr]
) extends Cmd

case class ProcDef(
    attrs: List[Attr],
    name: String,
    params: List[String],
    formals: List[(String, Type)],
    rets: List[(String, Type)],
    specs: List[Spec],
    body: Option[Prog]
) extends Cmd

object Axiom extends ((List[String], List[Attr], Expr) => Cmd)
object Lemma extends ((List[String], List[Attr], Expr) => Cmd)
object SortDef extends ((List[Attr], String, List[String], Option[Type]) => Cmd)
object ConstDef extends ((List[Attr], List[(String, Type)]) => Cmd)
object VarDef extends ((List[Attr], List[(String, Type)]) => Cmd)
object FunDef extends ((List[Attr], String, List[String], List[(String, Type)], Type, Option[Expr]) => Cmd)

// the grammar yields the specification and the body together,
// since the signature of a procedure ends with a semicolon exactly if there is no body
object ProcDef
    extends (
        (
            List[Attr],
            String,
            List[String],
            List[(String, Type)],
            List[(String, Type)],
            (List[Spec], Option[Prog])
        ) => Cmd
    ):
  def apply(
      attrs: List[Attr],
      name: String,
      params: List[String],
      formals: List[(String, Type)],
      rets: List[(String, Type)],
      contract: (List[Spec], Option[Prog])
  ): Cmd =
    val (specs, body) = contract
    ProcDef(attrs, name, params, formals, rets, specs, body)
