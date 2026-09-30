package cuvee.dafny

import cuvee.Error
import cuvee.core.State

object Grammar:
  import easyparse._
  import Brackets._

  val prefix_ops = Map(
    "-" -> 8,
    "!" -> 4
  )

  val postfix_ops = Map[String, Int](
    // "!" -> 8
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

  val translate = Map(
    "==" -> "=",
    "!" -> "not",
    "&&" -> "and",
    "||" -> "or",
    "==>" -> "=>",
    "<==>" -> "<=>",
    "/" -> "div",
    "%" -> "mod",
    "int" -> "Int",
    "bool" -> "Bool",
    "real" -> "Real"
  )

  val avoid =
    translate.values.toSet

  val Sym = (name: String) =>
    if translate.contains(name)
    then Grammar.translate(name)
    else if avoid.contains(name)
    then Error.raise("identifier invalid in Dafny", name)
    else name

  val kwd = T("kwd")
  val sym = T("sym")
  val num = Num(T("num"))
  val str = Str(T("str"))

  val id = Sym(sym)

  val nil = R(Nil)
  val none = R(None)

  def some[A](p: Parser[A]) =
    p.map { Some(_) }

  def left[A](p: Parser[A]) =
    p.map { Left(_) }

  def right[A](p: Parser[A]) =
    p.map { Right(_) }

  val la = id.filter(_ == "<").asScanner
  val ra = id.filter(_ == ">").asScanner

  def angle[A](p: Parser[A]) =
    la ~ p ~ ra

  val lit =
    P(num | str)

  val attrs =
    P(braces(":" ~ (id ~* ",")) | nil)

  val ids =
    P(id ~+ ",")

  val types =
    P(typ ~+ ",")

  val exprs =
    P(expr ~+ ",")

  val params =
    P(angle(ids) | nil)

  val inst =
    P(angle(types) | nil)

  val sort =
    Sort(P(id ~ inst))

  val typ: Parser[Type] =
    P(parens(typ) | sort)

  val formal =
    P(id ~ ":" ~ typ)

  val formals =
    P(parens(formal ~* ","))

  val args =
    P(parens(expr ~* ",") | nil)

  val array =
    Array(P(brackets(expr ~ (":=" ~ expr).?)))

  val member =
    Member(P("." ~ id ~ args))

  val access =
    P(array | member)

  val app =
    App(P(id ~ args ~ access.*))

  val true_ =
    R(True)

  val bool =
    R(Sort("Bool", Nil))

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

  val let =
    Let(P("var" ~ ids ~ ":=" ~ exprs ~ ";" ~ expr))

  val inner: Parser[Expr] =
    P(parens(expr) | lit | bind | let | app)

  val expr: Parser[Expr] =
    M(sym, prefix_ops, postfix_ops, infix_ops) $ (inner, (op, args) => App(Sym(op), args, Nil))

  val invariant =
    P("invariant" ~ expr)

  val requires =
    P("requires" ~ expr)

  val ensures =
    P("ensures" ~ expr)

  val modifies =
    P("modifies" ~ ids)

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

  val local =
    P("var" ~ (formal ~+ ",") ~ ";")

  val assign =
    Assign(P(ids ~ ":=" ~ exprs ~ ";"))

  val block =
    Block(P(braces(local.* ~ prog.*)))

  val else_block_or_skip =
    ("else" ~ block) | R(Skip)

  val if_ =
    If(P("if" ~ expr ~ block ~ else_block_or_skip))

  val while_ =
    While(P("while" ~ expr ~ invariant.* ~ block))

  val prog: Parser[Prog] =
    P(ctrl | spec | if_ | while_ | block | assign)

  val sel =
    Sel(P(id ~ ":" ~ typ))

  val sels =
    parens(sel ~* ",") | nil

  val constr =
    Constr(P(id ~ sels))

  val constrs =
    P(constr ~+ "|")

  val sortalias =
    P("=" ~ typ)

  val sortcmd =
    P(constdef | fundef | preddef | procdef)

  val sortimpl =
    P(braces(sortcmd.*) | nil)

  val sortdef =
    SortDef(P("type" ~ id ~ params ~ (right(sortimpl) | left(sortalias.?))))

  val datadef =
    DataDef(P("datatype" ~ id ~ params ~ "=" ~ constrs ~ sortimpl.?))

  val constdef =
    FunDef(P("const" ~ id ~ params ~ nil ~ ":" ~ typ ~ nil ~ nil ~ (":=" ~ expr).?))

  val fundef =
    FunDef(P("function" ~ id ~ params ~ formals ~ ":" ~ typ ~ requires.* ~ ensures.* ~ braces(expr).?))

  val preddef =
    FunDef(P("predicate" ~ id ~ params ~ formals ~ bool ~ requires.* ~ ensures.* ~ braces(expr).?))

  val axiom =
    Axiom(P("axiom" ~ expr))

  val returns =
    P("returns" ~ formals)

  val procdef =
    MethodDef(P("method" ~ id ~ params ~ formals ~ returns.? ~ modifies.* ~ requires.* ~ ensures.* ~ block.?))

  val cmd: Parser[Cmd] =
    P(sortdef | datadef | constdef | fundef | procdef | axiom)

  val script =
    P(cmd.*)
