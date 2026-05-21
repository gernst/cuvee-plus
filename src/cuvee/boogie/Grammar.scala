package cuvee.boogie

import cuvee.core.State

object Grammar extends cuvee.Grammar:
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

  val sort =
    P(id ~ inst) $ Syntax.app

  val array =
    P(brackets(typ) ~ typ) $ Syntax.binary("Array")

  val typ: Parser[Any] =
    P(sort | array)

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
    P("type" ~ id ~ params ~ ("=" ~ typ).? ~ ";") $ Syntax.sortdef

  val sel =
    P(id ~ ":" ~ typ) $ Syntax.pair

  val sels =
    parens(sel ~+ ",") | nil

  val constr =
    P(id ~ sels)

  val constrs =
    P(constr ~+ "|")

  val datadef =
    P("data" ~ id ~ params ~ "=" ~ constrs ~ ";") $ Syntax.datadef

  val funbody =
    some(braces(expr)) | none(";")

  val constdef =
    P("const" ~ id ~ params ~ nil ~ ":" ~ typ ~ funbody) $ Syntax.fundef
    
  val fundef =
    P("function" ~ id ~ params ~ formals ~ ":" ~ typ ~ funbody) $ Syntax.fundef

  val vardecl =
    P("var" ~ id ~ ":" ~ typ ~ ";") $ Syntax.binary("declare-var")

  val axiom =
    P("axiom" ~ expr ~ ";") $ Syntax.unary("assert")

  val sorry =
    S("sorry") $ Syntax.const("sorry")

  val proof =
    P(sorry)

  val lemmabody =
    some("proof" ~ proof) | none(";")

  val lemma =
    P("lemma" ~ attrs ~ params ~ expr ~ lemmabody) $ Syntax.lemma("lemma")

  val goal =
    P("goal" ~ attrs ~ params ~ expr ~ lemmabody) $ Syntax.lemma("prove")

  val cmd: Parser[Any] = 
    P(sortdef | datadef | constdef | fundef | vardecl | axiom | lemma | goal)

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
    "<==>" -> (Assoc.Left, 0),
    "==>" -> (Assoc.Right, 1),
    "||" -> (Assoc.Left, 2),
    "&&" -> (Assoc.Left, 3),
    "==" -> (Assoc.Left, 5),
    "!=" -> (Assoc.Left, 5),
    ">=" -> (Assoc.Left, 5),
    ">" -> (Assoc.Left, 5),
    "<" -> (Assoc.Left, 5),
    "<=" -> (Assoc.Left, 5),
    "+" -> (Assoc.Left, 6),
    "-" -> (Assoc.Left, 6),
    "*" -> (Assoc.Left, 7),
    "/" -> (Assoc.Left, 7),
    "%" -> (Assoc.Left, 7)
  )
