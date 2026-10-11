package cuvee.c

import easyparse.Assoc
import cuvee.Error

object Grammar:
  import easyparse._
  import Brackets._

  // the address &x and the dereference *p, which the parser rejects
  val prefix_ops = Map(
    "-" -> 13,
    "!" -> 13,
    "~" -> 13,
    "&" -> 13,
    "*" -> 13
  )

  val postfix_ops = Map[String, Int]()

  // the precedences of C, the bit operations below the comparisons, and the logical connectives of ACSL below those
  // of C, where implications associate to the right
  val infix_ops = Map(
    "<==>" -> (Assoc.Left, 0),
    "==>" -> (Assoc.Right, 1),
    "||" -> (Assoc.Left, 2),
    "&&" -> (Assoc.Left, 3),
    "|" -> (Assoc.Left, 4),
    "^" -> (Assoc.Left, 5),
    "&" -> (Assoc.Left, 6),
    "==" -> (Assoc.Left, 7),
    "!=" -> (Assoc.Left, 7),
    "<" -> (Assoc.Left, 8),
    "<=" -> (Assoc.Left, 8),
    ">" -> (Assoc.Left, 8),
    ">=" -> (Assoc.Left, 8),
    // shifts, by constants only (see Parser.arith)
    "<<" -> (Assoc.Left, 9),
    ">>" -> (Assoc.Left, 9),
    "+" -> (Assoc.Left, 10),
    "-" -> (Assoc.Left, 10),
    "*" -> (Assoc.Left, 11),
    "/" -> (Assoc.Left, 11),
    "%" -> (Assoc.Left, 11)
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

  val integer =
    P((J("int") | J("long") | J("short") | J("char") | J("unsigned") | J("signed")).+)

  val int: Parser[Type] =
    integer.map(IntType(_))

  val bool =
    BoolType("_Bool" | "bool")

  val void =
    VoidType("void")

  // e.g. __VERIFIER_nondet_double
  val float =
    FloatType("float" | "double")

  // the types of ACSL, which occur only in annotations
  val logic =
    Integer("integer") | BoolType("boolean")

  val base: Parser[Type] =
    P(float | int | bool | void | logic)

  val typ: Parser[Type] =
    P(qualifier.* ?~ base ~ qualifier.*)

  // the type of a declaration with the words of an integer type, which sizeof of its variables needs
  val sized: Parser[(Type, List[String])] =
    P(qualifier.* ?~ (integer.map(words => (IntType(words), words)) | base.map((_, Nil))) ~ qualifier.*)

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

  // the variables bound by a quantifier of ACSL, where a variable without type has that of the one before,
  // \forall integer i, j;
  val binders: Parser[List[(Type, String)]] =
    P((pointer.? ~ id) ~+ ",").map:
      _.foldLeft(List[(Type, String)]()):
        case (done, (Some(typ), x))           => done :+ (typ, x)
        case (done @ (_ :+ (typ, _)), (None, x)) => done :+ (typ, x)
        case (_, (None, x))                   => Error.raise("quantified variable without type", x)

  val quant =
    Quant(P((S("\\forall").map("forall") | S("\\exists").map("exists")) ~ binders ~ ";" ~ expr))

  // the terms of ACSL, which the scanner yields only in annotations
  val logical: Parser[Expr] =
    P(Result("\\result") | Old("\\old" ~ parens(expr)) | Id(S("\\true").map("true")) | Id(S("\\false").map("false")) | quant)

  val atom: Parser[Expr] =
    P(Num(num) | FloatNum(T("flt")) | sizeof | call | Id(id) | cast | parens(expr) | logical)

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
    P(J("=") | J("+=") | J("-=") | J("*=") | J("/=") | J("%=") | J("&=") | J("|=") | J("^=") | J("<<=") | J(">>="))

  val incr =
    P(J("++") | J("--"))

  val one = R(Num("1"))

  // assignments through pointers, *p = e, which the parser rejects
  val deref =
    App(P(star ~ unary.map(List(_))))

  // chained assignments x = y = e are the assignments y = e; x = y
  val assign: Parser[Stmt] =
    P((postfix | deref) ?~ assignop ~ (assign.map[Either[Expr, Stmt]](Right(_)) | expr.map(Left(_)))).map:
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
    Decl(P(sized ~ (declarator ~+ ",")))

  // the comma operator, e.g. i = 0, j = 0 in for loops, as a sequence of statements
  val simple: Parser[Stmt] =
    P(decl | P(single ~+ ",").map {
      case List(stmt) => stmt
      case stmts      => Block(stmts)
    })

  val single: Parser[Stmt] =
    P(assign | postincr | preincr | ExprStmt(expr))

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

  val goto_ =
    Goto(P("goto" ~ id ~ ";"))

  val switch_ =
    Switch(P("switch" ~ parens(expr) ~ braces(stmt.*)))

  val case_ =
    P("case" ~ expr ~ ":" ~ stmt).map((value, stmt) => Case(Some(value), stmt))

  val default_ =
    P("default" ~ ":" ~ stmt).map(Case(None, _))

  // the annotations of ACSL in function bodies: loops with their clauses, which may span several annotations, and
  // assertions, several in one annotation (see Parser.clauses)
  val loopclause =
    P("loop" ~ (P("invariant" ~ expr ~ ";").map(phi => Clause("loop invariant", Some(phi)))
      | P("variant" ~ expr ~ ";").map(e => Clause("loop variant", Some(e)))
      | ("assigns" ~ Until(";")).map(Clause("loop assigns", None))))

  val annotated =
    Annotated(P(("/*@" ?~ loopclause.+ ~ "*/").+.map(_.flatten) ~ (while_ | for_ | dowhile)))

  val assertion =
    P("/*@" ?~ P("assert" ~ expr ~ ";").+ ~ "*/").map:
      case List(phi) => Assertion(phi)
      case phis      => Block(phis.map(Assertion))

  val stmt: Parser[Stmt] =
    P(annotated | assertion | block | if_ | while_ | dowhile | for_ | switch_ | case_ | default_ | return_ | break_ | continue_ | goto_ | empty | labeled | (simple ~ ";"))

  // arrays of arrays as parameters, e.g. int a[][N]
  val param =
    P(pointer ~ id.? ~ brackets(expr.?).*).map:
      case ((typ, name), dims) => (dims.foldLeft(typ)((elem, _) => ArrayType(elem)), name)

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
    Global(Decl(P(sized ~ (declarator ~+ ",") ~ ";")))

  // the contract of ACSL of the function that follows
  val clause =
    P(P("requires" ~ expr ~ ";").map(phi => Clause("requires", Some(phi)))
      | P("ensures" ~ expr ~ ";").map(phi => Clause("ensures", Some(phi)))
      | P("decreases" ~ expr ~ ";").map(e => Clause("decreases", Some(e)))
      | ("assigns" ~ Until(";")).map(Clause("assigns", None)))

  val contract =
    Contract(P("/*@" ?~ clause.+ ~ "*/"))

  val typedef_ =
    Typedef("typedef" ~ Until(";"))

  val top: Parser[Top] =
    P(typedef_ | contract | function | global)

  // at least one declaration, such that a declaration that is not supported is a parse error,
  // where top.* would succeed without consuming input, which the pipeline then parses again forever
  val unit =
    P(top.+)
