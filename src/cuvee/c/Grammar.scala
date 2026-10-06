package cuvee.c

import easyparse.Assoc
import cuvee.Error

object Grammar:
  import easyparse._
  import Brackets._

  val prefix_ops = Map(
    "-" -> 11,
    "!" -> 11
  )

  val postfix_ops = Map[String, Int]()

  val infix_ops = Map(
    "||" -> (Assoc.Left, 2),
    "&&" -> (Assoc.Left, 3),
    "==" -> (Assoc.Left, 6),
    "!=" -> (Assoc.Left, 6),
    "<" -> (Assoc.Left, 7),
    "<=" -> (Assoc.Left, 7),
    ">" -> (Assoc.Left, 7),
    ">=" -> (Assoc.Left, 7),
    "+" -> (Assoc.Left, 9),
    "-" -> (Assoc.Left, 9),
    "*" -> (Assoc.Left, 10),
    "/" -> (Assoc.Left, 10),
    "%" -> (Assoc.Left, 10)
  )

  val sym = T("sym")
  val num = T("num")

  val id = sym.filter(name => name.head.isLetter || name.head == '_')

  val nil = R(Nil)

  val qualifier: Scanner =
    "const" | "static" | "extern" | "volatile"

  val intword: Scanner =
    "int" | "long" | "short" | "char" | "unsigned" | "signed"

  val int =
    IntType(intword.+)

  val bool =
    BoolType("_Bool" | "bool")

  val void =
    VoidType("void")

  val base: Parser[Type] =
    P(int | bool | void)

  val typ: Parser[Type] =
    P(qualifier.* ?~ base ~ qualifier.*)

  val args =
    P(parens(expr ~* ","))

  val call =
    Call(P(id ?~ args))

  val atom: Parser[Expr] =
    P(Num(num) | call | Id(id) | parens(expr))

  val postfix: Parser[Expr] =
    P(atom ~ brackets(expr).*).map:
      case (base, indices) => indices.foldLeft(base)(Index(_, _))

  val operators: Parser[Expr] =
    M(sym, prefix_ops, postfix_ops, infix_ops) $ (postfix, App)

  val expr: Parser[Expr] =
    Cond(P(operators ~ ("?" ~ expr ~ ":" ~ expr).?))

  val assignop =
    P(J("=") | J("+=") | J("-=") | J("*=") | J("/=") | J("%="))

  val incr =
    P(J("++") | J("--"))

  val one = R(Num("1"))

  val assign =
    Assign(P(postfix ?~ assignop ~ expr))

  val postincr =
    Assign(P(postfix ?~ incr ~ one))

  val preincr =
    P(incr ~ postfix).map:
      case (op, lhs) => Assign(lhs, op, Num("1"))

  val declarator =
    Declarator(P(id ~ brackets(expr.?).? ~ ("=" ~ expr).?))

  val decl =
    Decl(P(typ ~ (declarator ~+ ",")))

  val simple: Parser[Stmt] =
    P(decl | assign | postincr | preincr | ExprStmt(expr))

  val block =
    Block(P(braces(stmt.*)))

  val if_ =
    If(P("if" ~ parens(expr) ~ stmt ~ ("else" ~ stmt).?))

  val while_ =
    While(P("while" ~ parens(expr) ~ stmt))

  val dowhile =
    DoWhile(P("do" ~ stmt ~ "while" ~ parens(expr) ~ ";"))

  val for_ =
    For(P("for" ~ "(" ~ simple.? ~ ";" ~ expr.? ~ ";" ~ simple.? ~ ")" ~ stmt))

  val return_ =
    Return(P("return" ~ expr.? ~ ";"))

  val break_ =
    Break("break" ~ ";")

  val continue_ =
    Continue("continue" ~ ";")

  val empty =
    Empty(";")

  val stmt: Parser[Stmt] =
    P(block | if_ | while_ | dowhile | for_ | return_ | break_ | continue_ | empty | (simple ~ ";"))

  val param =
    P(typ ~ id ~ (brackets(expr.?).map(_ => true) | R(false))).map:
      case ((typ, name), true)  => (ArrayType(typ), name)
      case ((typ, name), false) => (typ, name)

  val params =
    P(parens("void".map(Nil) | (param ~* ",")))

  val function =
    Function(P(typ ~ id ?~ params ~ (block.map(Some(_)) | ";".map(None))))

  val global =
    Global(Decl(P(typ ~ (declarator ~+ ",") ~ ";")))

  val top: Parser[Top] =
    P(function | global)
