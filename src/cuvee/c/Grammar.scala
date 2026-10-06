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

  val star = sym.filter(_ == "*")

  // a balanced sequence of tokens in brackets, which is skipped
  case class Balanced(open: String, close: String) extends Scanner:
    def scan(in: Input, cm: Boolean): Input =
      in match
        case Token.Keyword(`open`) #:: rest =>
          var depth = 1
          var in_ = rest

          while depth > 0
          do
            in_ match
              case Token.Keyword(`open`) #:: rest  => depth += 1; in_ = rest
              case Token.Keyword(`close`) #:: rest => depth -= 1; in_ = rest
              case _ #:: rest                      => in_ = rest
              case _                               => Input.fail("'" + close + "'", in_, true)

          in_

        case _ =>
          Input.fail("'" + open + "'", in, cm)

  // the parser `next(a)` after `first` has parsed `a`, committed as with ~
  case class Dependent[A, B](first: Parser[A], next: A => Parser[B]) extends Parser[B]:
    def parse(in: Input, cm: Boolean) =
      val (a, in_) = first.parse(in, cm)
      next(a).parse(in_, true)

  // the tokens up to `end`, outside of braces, which are skipped
  case class Until(end: String) extends Scanner:
    def scan(in: Input, cm: Boolean): Input =
      var depth = 0
      var in_ = in

      while true
      do
        in_ match
          case Token.Keyword(`end`) #:: rest if depth == 0 => return rest
          case Token.Keyword("{") #:: rest                 => depth += 1; in_ = rest
          case Token.Keyword("}") #:: rest                 => depth -= 1; in_ = rest
          case _ #:: rest                                  => in_ = rest
          case _                                           => Input.fail("'" + end + "'", in_, true)

      in_

  // __attribute__((...)) of GCC, which is ignored
  val attribute: Scanner =
    "__attribute__" ~ Balanced("(", ")")

  val qualifier: Scanner =
    "const" | "static" | "extern" | "volatile" | "inline" | "restrict" | attribute

  val intword: Scanner =
    "int" | "long" | "short" | "char" | "unsigned" | "signed"

  val int =
    IntType(intword.+)

  val bool =
    BoolType("_Bool" | "bool")

  val void =
    VoidType("void")

  // e.g. __VERIFIER_nondet_double
  val float =
    FloatType("float" | "double")

  val base: Parser[Type] =
    P(float | int | bool | void)

  val typ: Parser[Type] =
    P(qualifier.* ?~ base ~ qualifier.*)

  // pointers occur in the signatures of the builtins of the harness of SV-COMP, e.g. __assert_fail
  val pointer: Parser[Type] =
    P(typ ~ (star ~ qualifier.*).*).map:
      case (typ, stars) => stars.foldLeft(typ)((elem, _) => PointerType(elem))

  val args =
    P(parens(expr ~* ","))

  val call =
    Call(P(id ?~ args))

  // the operand of a cast is a unary expression: an operand, a prefix operator, or another cast
  val unary: Parser[Expr] =
    P(cast | operand | App(sym.filter(prefix_ops.contains) ~ unary.map(List(_))))

  val cast: Parser[Expr] =
    Cast(P("(" ?~ pointer ~ ")" ~ unary))

  val intwords =
    P((J("int") | J("long") | J("short") | J("char") | J("unsigned") | J("signed") | J("_Bool") | J("bool")).+)

  val sizeof: Parser[Expr] =
    P("sizeof" ~ (SizeofType("(" ?~ (qualifier.* ?~ intwords) ~ qualifier.* ~ ")") | SizeofExpr(unary)))

  val atom: Parser[Expr] =
    P(Num(num) | sizeof | call | Id(id) | cast | parens(expr))

  val postfix: Parser[Expr] =
    P(atom ~ brackets(expr).*).map:
      case (base, indices) => indices.foldLeft(base)(Index(_, _))

  // postfix expressions, which may be incremented or decremented, e.g. counter++ < 10
  val operand: Parser[Expr] =
    P(incremented | P(postfix ~ incr.?).map {
      case (lhs, Some(op)) => Incr(lhs, op, true)
      case (e, None)       => e
    })

  val incremented: Parser[Expr] =
    P(incr ~ postfix).map((op, lhs) => Incr(lhs, op, false))

  val operators: Parser[Expr] =
    M(sym, prefix_ops, postfix_ops, infix_ops) $ (operand, App)

  val expr: Parser[Expr] =
    Cond(P(operators ~ ("?" ~ expr ~ ":" ~ expr).?))

  val assignop =
    P(J("=") | J("+=") | J("-=") | J("*=") | J("/=") | J("%="))

  val incr =
    P(J("++") | J("--"))

  val one = R(Num("1"))

  // chained assignments x = y = e are the assignments y = e; x = y
  val assign: Parser[Stmt] =
    P(postfix ?~ assignop ~ (assign.map[Either[Expr, Stmt]](Right(_)) | expr.map(Left(_)))).map:
      case ((lhs, op), Left(rhs))    => Assign(lhs, op, rhs)
      case ((lhs, op), Right(inner)) => Block(List(inner, Assign(lhs, op, target(inner))))

  def target(assign: Stmt): Expr =
    assign match
      case Assign(lhs, _, _) => lhs
      case Block(stmts)      => target(stmts.last)
      case _                 => Error.raise("not an assignment", assign)

  val postincr =
    Assign(P(postfix ?~ incr ~ one))

  val preincr =
    P(incr ~ postfix).map:
      case (op, lhs) => Assign(lhs, op, Num("1"))

  val init: Parser[Expr] =
    P(Items(braces(init ~* ",")) | expr)

  val declarator =
    Declarator(P(star.?.map(_.isDefined) ~ id ~ brackets(expr.?).* ~ ("=" ~ init).?))

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

  val labeled =
    Labeled(P(id ?~ ":" ~ stmt))

  val stmt: Parser[Stmt] =
    P(block | if_ | while_ | dowhile | for_ | return_ | break_ | continue_ | empty | labeled | (simple ~ ";"))

  val param =
    P(pointer ~ id.? ~ (brackets(expr.?).map(_ => true) | R(false))).map:
      case ((typ, name), true)  => (ArrayType(typ), name)
      case ((typ, name), false) => (typ, name)

  // parameters without names, as in declarations, are named by their position
  val params =
    P(parens(param ~* ",")).map:
      case List((VoidType, None)) => Nil
      case params =>
        for ((typ, name), i) <- params.zipWithIndex
        yield (typ, name.getOrElse("_" + i))

  val header =
    P(pointer ~ id ?~ params ~ attribute.*)

  // the bodies of builtins are skipped, as they are not resolved (see Syntax.builtin),
  // which spares the grammar the constructs of the preprocessed assert.h, e.g. ({ ... }) and sizeof
  def body(name: String): Parser[Option[Block]] =
    if Syntax.builtin(name)
    then Balanced("{", "}").map(Some(Block(Nil))) | ";".map(None)
    else block.map(Some(_)) | ";".map(None)

  val function: Parser[Top] =
    P(Dependent(header, { case ((typ, name), params) => body(name).map(Function(typ, name, params, _)) }))

  val global =
    Global(Decl(P(typ ~ (declarator ~+ ",") ~ ";")))

  val typedef_ =
    Typedef("typedef" ~ Until(";"))

  val top: Parser[Top] =
    P(typedef_ | function | global)

  // at least one declaration, such that a declaration that is not supported is a parse error,
  // where top.* would succeed without consuming input, which the pipeline then parses again forever
  val unit =
    P(top.+)
