package cuvee.dafny

import cuvee.core.State

object Grammar extends cuvee.pipe.Grammar:
  import easyparse._
  import Brackets._

  val init = State.empty

  val prefix_ops = Map(
    "-" -> 8,
    "!" -> 4
  )

  val postfix_ops = Map(
    "!" -> 8
  )

  val infix_ops = Map(
    "<==>" -> (Assoc.Non, 0),
    "==>" -> (Assoc.Right, 1),
    "||" -> (Assoc.Left, 2),
    "&&" -> (Assoc.Left, 3),
    "==" -> (Assoc.Left, 5),
    "!=" -> (Assoc.Left, 5),
    ">=" -> (Assoc.Non, 5),
    ">" -> (Assoc.Non, 5),
    "<" -> (Assoc.Non, 5),
    "<=" -> (Assoc.Non, 5),
    "+" -> (Assoc.Left, 6),
    "-" -> (Assoc.Left, 6),
    "*" -> (Assoc.Left, 7),
    "/" -> (Assoc.Left, 7),
    "%" -> (Assoc.Left, 7)
  )

  val kwd = T("kwd")
  val sym = T("sym")
  val num = Num(T("num"))
  val str = Str(T("str"))

  val nil = R(Nil)

  def none(s: Scanner) =
    None(s)

  def some[A](p: Parser[A]) =
    Some(p)

  val star = sym.filter(_ == "*").asScanner
  val la = sym.filter(_ == "<").asScanner
  val ra = sym.filter(_ == ">").asScanner

  def angle[A](p: Parser[A]) =
    la ~ p ~ ra

  val lit =
    P(num | str)

  val attrs =
    P(braces(":" ~ (sym ~* ",")) | nil)

  val syms =
    P(sym ~+ ",")

  val types =
    P(typ ~+ ",")

  val exprs =
    P(expr ~+ ",")

  val params =
    P(angle(syms) | nil)

  val inst =
    P(angle(types) | nil)

  val typ: Parser[Type] =
    Sort(P(sym ~ inst))

  val formal =
    P(sym ~ ":" ~ typ)

  val formals =
    P(parens(formal ~* ","))

  val args =
    P(parens(exprs) | nil)

  val access =
    P(brackets(expr ~ (":=" ~ expr).?))

  val app =
    App(P(sym ~ args ~ access.*))

  val true_ =
    R(True)

  val else_expr_or_true =
    ("else" ~ expr) | true_

  val ite =
    Ite(P("if" ~ expr ~ "then" ~ expr ~ else_expr_or_true))

  val forall =
    All(P("forall" ~ formals ~ "::" ~ expr))

  val exists =
    Ex(P("exists" ~ formals ~ "::" ~ expr))

  val bind =
    P(forall | exists)

  val inner: Parser[Expr] =
    P(parens(expr) | lit | bind | app)

  val expr: Parser[Expr] =
    M(sym, prefix_ops, postfix_ops, infix_ops) $ (inner, App(_, _, Nil))

  val invariant =
    P("invariant" ~ expr)

  val requires =
    P("requires" ~ expr)

  val ensures =
    P("ensures" ~ expr)

  val modifies =
    P("modifies" ~ syms)

  val break =
    Break("break" ~ ";")

  val return_ =
    Return("return" ~ ";")

  val continue =
    Continue("continue" ~ ";")

  val ctrl =
    P(break | return_ | continue)

  val assume =
    Assume(P("assume" ~ expr ~ ";"))

  val assert =
    Assert(P("assert" ~ expr ~ ";"))

  val spec =
    P(assume | assert)

  val nondet =
    Nondet(star)

  val rhs =
    P(nondet | expr)

  val assign =
    Assign(P(syms ~ ":=" ~ (rhs ~+ ",")))

  val block =
    Block(P(braces(prog.*)))

  val else_block_or_skip =
    ("else" ~ block) | R(Skip)

  val if_ =
    If(P("if" ~ expr ~ block ~ else_block_or_skip))

  val while_ =
    While(P("while" ~ expr ~ invariant.* ~ block))

  val prog: Parser[Prog] =
    P(ctrl | spec | if_ | while_ | block | assign)

  val sel =
    Sel(P(sym ~ ":" ~ typ))

  val sels =
    parens(sel ~+ ",") | nil

  val constr =
    Constr(P(sym ~ sels))

  val constrs =
    P(constr ~+ "|")

  val sortdef =
    SortDef(P("type" ~ sym ~ params ~ ("=" ~ typ).?))

  val datadef =
    DataDef(P("datatype" ~ sym ~ params ~ "=" ~ constrs))

  val constdef =
    FunDef(P("const" ~ sym ~ params ~ nil ~ ":" ~ typ ~ nil ~ nil ~ (":=" ~ expr).?))

  val fundef =
    FunDef(P("function" ~ sym ~ params ~ formals ~ ":" ~ typ ~ requires.* ~ ensures.* ~ braces(expr).?))

  val axiom =
    Axiom(P("axiom" ~ expr))

  val returns =
    P("returns" ~ formals)

  val procdef =
    MethodDef(P("method" ~ sym ~ params ~ formals ~ returns.? ~ modifies.* ~ requires.* ~ ensures.* ~ braces(prog).?))

  val cmd: Parser[Cmd] =
    P(sortdef | datadef | constdef | fundef | procdef | axiom)

  val script =
    P(cmd.*)
