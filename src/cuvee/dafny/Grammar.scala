package cuvee.dafny

import cuvee.core.State
import cuvee.boogie.Syntax

object Grammar extends cuvee.pipe.Grammar:
  import easyparse._
  import Brackets._

  val init = State.default

  val sym = T("sym")
  val num = T("int") $ { BigInt(_) }

  val nil = R(Nil)

  def none(s: Scanner) =
    s $ { None }

  def some[A](p: Parser[A]) =
    p $ { Some(_) }

  val la = sym.filter (_ == "<").asScanner
  val ra = sym.filter (_ == ">").asScanner

  def angle[A](p: Parser[A]) =
    la ~ p ~ ra

  val kw = sym $ Syntax.kw
  val id = sym $ Syntax.id

  val attrs =
    P(braces(":" ~ (kw ~* ",")) | nil)

  val params =
    P(angle(id ~+ ",") | nil)

  val inst =
    P(angle(typ ~+ ",") | nil)

  val typ: Parser[Any] =
    P(id ~ inst) $ Syntax.app

  val formal =
    P(id ~ ":" ~ typ) $ Syntax.pair

  val formals =
    P(parens(formal ~* ","))

  val args =
    P(parens(expr ~+ ",") | nil)

  val access =
    P(brackets(expr ~ (":=" ~ expr).?))

  val app =
    P(id ~ args ~ access.*) $ Syntax.app

  val true_ =
    R(Syntax.const("true"))

  val else_expr_or_true =
    ("else" ~ expr) | true_

  val ite =
    P("if" ~ expr ~ "then" ~ expr ~ else_expr_or_true) $ Syntax.ternary("ite")

  val forall =
    P("forall" ~ formals ~ "::" ~ expr) $ Syntax.binary("forall")

  val exists =
    P("exists" ~ formals ~ "::" ~ expr) $ Syntax.binary("exists")

  val bind =
    P(forall | exists)

  val inner: Parser[Any] =
    P(parens(expr) | bind | app)

  val expr: Parser[Any] =
    M(sym, prefix_ops, postfix_ops, infix_ops) $ (inner, Syntax.infix)

  val sortdef =
    P("type" ~ id ~ params ~ ("=" ~ typ).?) $ Syntax.sortdef

  val sel =
    P(id ~ ":" ~ typ) $ Syntax.pair

  val sels =
    parens(sel ~+ ",") | nil

  val constr =
    P(id ~ sels)

  val constrs =
    P(constr ~+ "|")

  val datadef =
    P("datatype" ~ id ~ params ~ "=" ~ constrs) $ Syntax.datadef

  val constdef =
    P("const" ~ id ~ params ~ nil ~ ":" ~ typ ~ (":=" ~ expr).?) $ Syntax.fundef
    
  val fundef =
    P("function" ~ id ~ params ~ formals ~ ":" ~ typ ~ braces(expr).?) $ Syntax.fundef

  val axiom =
    P("axiom" ~ expr) $ Syntax.unary("assert")

  val cmd: Parser[Any] = 
    P(sortdef | datadef | constdef | fundef | axiom)

  val script =
    P(cmd.*)

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
