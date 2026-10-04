package cuvee.c

import easyparse.Assoc

object Grammar:
  import easyparse._
  import Brackets._

  // the precedences of C, where the conditional ?: is parsed separately on top
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

  // qualifiers and storage classes are ignored, all integer types are int
  val qualifier =
    P("const".map(()) | "static".map(()) | "extern".map(()) | "volatile".map(()))

  val intword =
    P("int".map(()) | "long".map(()) | "short".map(()) | "char".map(()) | "unsigned".map(()) | "signed".map(()))

  val base: Parser[Type] =
    P(intword.+.map(_ => IntType) | "_Bool".map(BoolType) | "bool".map(BoolType) | "void".map(VoidType))

  // backtracks if there is no type after the qualifiers
  val typ: Parser[Type] =
    P(qualifier.* ?~ base ~ qualifier.*).map:
      case ((_, typ), _) => typ

  val args =
    P(parens(expr ~* ","))

  // backtracks if there are no arguments, which is then a variable
  val call =
    Call(P(id ?~ args))

  val atom: Parser[Expr] =
    P(Num(num) | call | Id(id) | parens(expr))

  // array accesses a[i]
  val postfix: Parser[Expr] =
    P(atom ~ brackets(expr).*).map:
      case (base, indices) => indices.foldLeft(base)(Index(_, _))

  val operators: Parser[Expr] =
    M(sym, prefix_ops, postfix_ops, infix_ops) $ (postfix, {
      case (op, List(arg))         => Unary(op, arg)
      case (op, List(left, right)) => Binary(op, left, right)
      case (op, args)              => cuvee.Error.raise("unexpected operator application", op, args)
    })

  val expr: Parser[Expr] =
    P(operators ~ ("?" ~ expr ~ ":" ~ expr).?).map:
      case (expr, None)                => expr
      case (test, Some((left, right))) => Cond(test, left, right)

  val assignop =
    P("=".map("=") | "+=".map("+") | "-=".map("-") | "*=".map("*") | "/=".map("/") | "%=".map("%"))

  // increments and decrements, x++ and ++x, are x += 1 and x -= 1
  val incr =
    P("++".map("+") | "--".map("-"))

  val one = R(Num("1"))

  // simple statements without the semicolon, which are also the headers of for loops;
  // assignments backtrack if there is no assignment operator after the left hand side, which is then an expression
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
    P(decl | assign | postincr | preincr | expr.map(ExprStmt))

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

  val stmt: Parser[Stmt] =
    P(
      block | if_ | while_ | dowhile | for_ | return_ |
        ("break" ~ ";").map(Break) | ("continue" ~ ";").map(Continue) | ";".map(Empty) | (simple ~ ";")
    )

  // array parameters are written a[] or a[n], whose size is ignored
  val param =
    P(typ ~ id ~ (brackets(expr.?).map(_ => true) | R(false))).map:
      case ((typ, name), true)  => (ArrayType(typ), name)
      case ((typ, name), false) => (typ, name)

  val params =
    P(parens("void".map(Nil) | (param ~* ",")))

  // functions and global variables share the type and the first name
  val function =
    P(params ~ (block.map(Some(_)) | ";".map(None)))

  val global =
    P(brackets(expr.?).? ~ ("=" ~ expr).? ~ ("," ~ declarator).* ~ ";")

  val top: Parser[Top] =
    P(typ ~ id ~ (function.map(Left(_)) | global.map(Right(_)))).map:
      case ((typ, name), Left((params, body))) =>
        Function(typ, name, params, body)

      case ((typ, name), Right(((size, init), rest))) =>
        Global(Decl(typ, Declarator(name, size, init) :: rest))

  // the whole translation unit at once, such that the global variables modified by functions can be inferred
  val unit =
    P(top.*)
