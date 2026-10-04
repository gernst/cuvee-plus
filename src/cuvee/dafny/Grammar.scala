package cuvee.dafny

import cuvee.Error
import cuvee.core.State

object Grammar:
  import easyparse._
  import Brackets._

  // prefix operators bind tighter than all infix operators, as in Dafny
  val prefix_ops = Map(
    "-" -> 8,
    "!" -> 8
  )

  val postfix_ops = Map[String, Int](
    // "!" -> 8
  )

  // chained equations and comparisons as in Dafny, e.g. x == y == z or x < y <= z, are not supported for now:
  // == and != associate to the left as boolean operators, and the comparisons do not associate
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
    "in" -> (Assoc.Non, 5),
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
    "real" -> "Real",
    "seq" -> "Seq",
    "array" -> "Array"
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
  val num = T("num")
  val dec = T("dec")
  val str = T("str")

  val id = Sym(sym)

  val prime = sym.filter(_ == "'").asScanner

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
    P(Num(num) | Dec(dec) | Str(str))

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
    Member(P("." ~ (id | num) ~ args))

  // backtracks if there is no .. after the lower bound, which is then an array access
  val slice =
    Slice(P(("[" ?~ expr.? ?~ "..") ~ expr.? ~ "]"))

  val access =
    P(slice | array | member)

  val app =
    App(P(id ~ args ~ access.*))

  val true_ =
    R(True)

  val bool =
    R(Sort("Bool", Nil))

  val else_expr_or_true =
    P(("else" ~ expr) | true_)

  val ite =
    Ite(P("if" ~ expr ~ "then" ~ expr ~ else_expr_or_true))

  // the bound variables of quantifiers, with or without parentheses
  val bound =
    P(formals | (formal ~+ ","))

  val forall =
    All(P("forall" ~ bound ~ "::" ~ expr))

  val exists =
    Ex(P("exists" ~ bound ~ "::" ~ expr))

  val bind =
    P(forall | exists)

  // the bound variables of let expressions have explicit types, var x: T := e; body
  val let =
    Let(P("var" ~ (formal ~+ ",") ~ ":=" ~ exprs ~ ";" ~ expr))

  // parenthesized expressions, which are tuples if there is more than one
  val tuple =
    Tuple(P(parens(exprs)))

  // derivatives (x, y :: e)' with explicit variables,
  // backtracks if there is no :: after the variables, e.g. for parenthesized expressions and tuples
  val diff =
    Diff(P(("(" ?~ ids ?~ "::") ~ expr ~ ")" ~ prime))

  val seq =
    SeqLit(P(brackets(expr ~* ",")))

  val len =
    Len(P("|" ~ expr ~ "|"))

  val atom: Parser[Expr] =
    P(diff | tuple | seq | len | lit | bind | let | ite | combinator | app)

  // indexing and slices of other atoms than names and calls, which take their accesses themselves,
  // members and testers are accessed on variables only
  val accessed: Parser[Expr] =
    P(atom ~ (slice | array).*).map:
      case (expr, Nil)    => expr
      case (expr, access) => Access_(expr, access)

  // type annotations bind tighter than all operators
  def word(name: String) =
    id.filter(_ == name)

  val arrow = sym.filter(_ == "=>").asScanner

  // the cases of an update, if guard then result, ..., which backtrack if followed by else,
  // which is then an if-then-else expression, an update with a single case is just its result;
  // the update ends the combinator, hence the closing parenthesis
  val guarded =
    P(("if" ?~ expr ?~ "then") ?~ expr)

  val update: Parser[List[(Expr, Expr)]] =
    P(((guarded ~+ ",") ?~ ")") | (expr.map(e => List((App("true", Nil, Nil), e))) ~ ")"))

  // backtracks until for, the combinators may be names of functions otherwise
  val trace_ =
    P((word("trace") ?~ "(" ?~ expr ?~ "," ?~ word("for")) ~ exprs ~ word("do").asScanner ~ ids ~ arrow ~ update).map:
      case ((((((_, init), _), deps), bound), update)) => Combinator("trace", Some(init), deps, bound, update)

  val map_ =
    P((word("map") ?~ "(" ?~ word("for")) ~ exprs ~ word("yield").asScanner ~ ids ~ arrow ~ update).map:
      case ((((_, deps), bound), update)) => Combinator("map", None, deps, bound, update)

  val all_ =
    P((word("all") ?~ "(" ?~ word("for")) ~ exprs ~ word("check").asScanner ~ ids ~ arrow ~ expr ~ ")").map:
      case ((((_, deps), bound), body)) => Combinator("all", None, deps, bound, List((App("true", Nil, Nil), body)))

  val combinator =
    P(trace_ | map_ | all_)

  val inner: Parser[Expr] =
    P(accessed ~ ("as" ~ typ).?).map:
      case (expr, None)      => expr
      case (expr, Some(typ)) => As(expr, typ)

  val expr: Parser[Expr] =
    M(sym, prefix_ops, postfix_ops, infix_ops) $ (inner, (op, args) => App(Sym(op), args, Nil))

  // expressions with operators that bind tighter than conjunction
  val term: Parser[Expr] =
    M(sym, prefix_ops, postfix_ops, infix_ops, min = infix_ops("&&")._2 + 1) $ (inner, (op, args) => App(Sym(op), args, Nil))

  val invariant =
    P("invariant" ~ expr)

  val requires =
    P("requires" ~ expr)

  val ensures =
    P("ensures" ~ expr)

  // a lexicographic termination measure
  val decreases =
    P("decreases" ~ exprs)

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
    Local(P("var" ~ (formal ~+ ",") ~ (":=" ~ exprs).? ~ ";"))

  // backtracks if there is no :=, which is then a call statement
  val assign =
    Assign(P(ids ?~ ":=" ~ exprs ~ ";"))

  // method calls without results, represented as assignments to no variables
  val call =
    Assign(P(nil ?~ app.map(List(_)) ~ ";"))

  val block =
    Block(P(braces(local.* ~ prog.*)))

  // else if chains are nested if statements
  val else_block_or_skip =
    P(("else" ~ (if_ | block)) | R(Skip))

  // the guard * of a choice or of nondeterministic iterations
  val star = id.filter(_ == "*").asScanner

  val guard =
    P(star.map(None) | some(expr))

  val if_ : Parser[Prog] =
    If(P("if" ~ guard ~ block ~ else_block_or_skip))

  val while_ =
    While(P("while" ~ guard ~ invariant.* ~ decreases.* ~ block))

  val eq = sym.filter(_ == "==").asScanner
  val and = sym.filter(_ == "&&").asScanner

  // backtracks if there is no prime after the first variable, which is then an assignment or call statement;
  // the right hand sides bind tighter than the conjunction with the evolution constraint
  val ode =
    Ode(P(((id ?~ prime) ~+ ",") ~ eq ~ (term ~+ ",") ~ (and ~ expr).? ~ invariant.* ~ ";"))

  val par =
    Par(P("parallel" ~ braces((assign | call).*)))

  val prog: Parser[Prog] =
    P(ctrl | spec | if_ | while_ | par | block | ode | assign | call)

  val sel =
    Sel(P((id | num) ~ ":" ~ typ))

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
    SortDef(P("type" ~ id ~ params ~ (right(braces(sortcmd.*)) | left(sortalias.?))))

  val datadef =
    DataDef(P("datatype" ~ id ~ params ~ "=" ~ constrs ~ sortimpl.?))

  val constdef =
    FunDef(P("const" ~ id ~ params ~ nil ~ ":" ~ typ ~ nil ~ nil ~ nil ~ (":=" ~ expr).?))

  val fundef =
    FunDef(P("function" ~ id ~ params ~ formals ~ ":" ~ typ ~ requires.* ~ ensures.* ~ decreases.* ~ braces(expr).?))

  val preddef =
    FunDef(P("predicate" ~ id ~ params ~ formals ~ bool ~ requires.* ~ ensures.* ~ decreases.* ~ braces(expr).?))

  val axiom =
    Axiom(P("axiom" ~ expr))

  val vardef =
    VarDef(P("var" ~ (formal ~+ ",") ~ ";"))

  val returns =
    P("returns" ~ formals)

  val assumes =
    P("assumes" ~ expr)

  val commits =
    P("commits" ~ expr)

  val procdef =
    MethodDef(P("method" ~ id ~ params ~ formals ~ returns.? ~ modifies.* ~ requires.* ~ ensures.* ~ assumes.* ~ commits.* ~ decreases.* ~ block.?))

  val cmd: Parser[Cmd] =
    P(sortdef | datadef | constdef | fundef | preddef | procdef | axiom | vardef)

  val script =
    P(cmd.*)
