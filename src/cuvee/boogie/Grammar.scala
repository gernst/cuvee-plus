package cuvee.boogie

import util.Name
import cuvee.Error

object Grammar:
  import easyparse._
  import Brackets._

  // prefix operators bind tighter than all infix operators, as in Boogie
  val prefix_ops = Map(
    "-" -> 8,
    "!" -> 8
  )

  val postfix_ops = Map[String, Int]()

  // Boogie puts && and || on the same level and rejects mixing them without parentheses,
  // here && binds tighter as in Dafny, which accepts more programs;
  // reverse implication <== is not supported
  val infix_ops = Map(
    "<==>" -> (Assoc.Left, 0),
    "==>" -> (Assoc.Right, 1),
    "||" -> (Assoc.Left, 2),
    "&&" -> (Assoc.Left, 3),
    "==" -> (Assoc.Non, 5),
    "!=" -> (Assoc.Non, 5),
    ">=" -> (Assoc.Non, 5),
    ">" -> (Assoc.Non, 5),
    "<" -> (Assoc.Non, 5),
    "<=" -> (Assoc.Non, 5),
    "+" -> (Assoc.Left, 6),
    "-" -> (Assoc.Left, 6),
    "*" -> (Assoc.Left, 7),
    "/" -> (Assoc.Left, 7),
    "div" -> (Assoc.Left, 7),
    "mod" -> (Assoc.Left, 7)
  )

  val translate = Map(
    "==" -> "=",
    "!" -> "not",
    "&&" -> "and",
    "||" -> "or",
    "==>" -> "=>",
    "<==>" -> "<=>",
    "int" -> "Int",
    "real" -> "Real",
    "bool" -> "Bool",
    "array" -> "Array"
  )

  val avoid =
    translate.values.toSet

  // trailing subscripts denote the index of a name, e.g. x₀ is x$0, which is the internal form of indexed names,
  // see util.Name, such that names print and parse back the same
  val subscripted = "(.+?)([₀-₉]+)".r

  def index(name: String) =
    name match
      case subscripted(base, digits) =>
        // digits.map would convert the string to a scanner, see easyparse
        val index = digits.toSeq.map(Name.subscripts.indexOf(_)).mkString
        Name(base, Some(index.toInt)).indexed

      case _ =>
        name

  val Sym = (name: String) =>
    if translate.contains(name)
    then Grammar.translate(name)
    else if avoid.contains(name)
    then Error.raise("identifier invalid in Boogie", name)
    else index(name)

  val sym = T("sym")
  val num = T("num")
  val dec = T("dec")
  val str = T("str")

  val id = Sym(sym)

  val nil = R(Nil)
  val none = R(None)

  def some[A](p: Parser[A]) =
    p.map { Some(_) }

  // symbols that are not keywords, e.g. < and > of type parameters
  def op(name: String) =
    id.filter(_ == name).asScanner

  val la = op("<")
  val ra = op(">")

  def angle[A](p: Parser[A]) =
    la ~ p ~ ra

  // groups of variables with a common type, x, y: int, b: bool
  def flatten(groups: List[(List[String], Type)]) =
    for
      (xs, typ) <- groups;
      x <- xs
    yield (x, typ)

  val ids =
    P(id ~+ ",")

  val exprs =
    P(expr ~+ ",")

  val params =
    P(angle(ids) | nil)

  val array =
    Array(P(brackets(typ) ~ typ))

  val types =
    P(typ ~+ ",")

  // type arguments are in angle brackets, e.g. List<int>, unlike in Boogie
  val sort =
    Sort(P(id ~ (angle(types) | nil)))

  val typ: Parser[Type] =
    P(array | parens(typ) | sort)

  val typed =
    P((ids ~ ":" ~ typ) ~+ ",").map(flatten)

  val formals =
    P(parens(typed | nil))

  val args =
    P(parens(expr ~* ","))

  val lit =
    P(Num(num) | Dec(dec) | Str(str))

  // map selection and update, a[i] and a[i := v]
  val access =
    Access(P(brackets(expr ~ (":=" ~ expr).?)))

  val app =
    App(P(id ~ (args | nil) ~ access.*))

  val trigger =
    P(braces(exprs))

  val binding =
    P(typed ~ "::" ~ trigger.* ~ expr)

  val forall =
    All(P("forall" ~ binding))

  val exists =
    Ex(P("exists" ~ binding))

  // quantifiers are always in parentheses
  val parenthesized =
    P("(" ~ (forall | exists | expr) ~ ")")

  val ite =
    Ite(P("if" ~ expr ~ "then" ~ expr ~ "else" ~ expr))

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

  // all but the last element of a trace
  val butlast =
    Butlast(P("⌊" ~ expr ~ "⌋"))

  val inner: Parser[Expr] =
    P(lit | parenthesized | ite | butlast | combinator | app)

  val expr: Parser[Expr] =
    M(sym, prefix_ops, postfix_ops, infix_ops) $ (inner, (op, args) => App(Sym(op), args, Nil))

  val requires =
    Requires(P("requires" ~ expr ~ ";"))

  val ensures =
    Ensures(P("ensures" ~ expr ~ ";"))

  val invariant =
    Invariant(P("invariant" ~ expr ~ ";"))

  val modifies =
    Modifies(P("modifies" ~ ids ~ ";"))

  val break =
    Break("break" ~ ";")

  val return_ =
    Return("return" ~ ";")

  val assume =
    Assume(P("assume" ~ expr ~ ";"))

  val assert =
    Assert(P("assert" ~ expr ~ ";"))

  val havoc =
    Havoc(P("havoc" ~ ids ~ ";"))

  // the results are optional, call p(x); and call y := p(x);
  val call =
    Call(P("call" ~ ((ids ?~ ":=") | nil) ~ id ~ args ~ ";"))

  val lhs =
    Lhs(P(id ~ brackets(expr).*))

  val assign =
    Assign(P((lhs ~+ ",") ~ ":=" ~ exprs ~ ";"))

  // local variables, var x, y: int, b: bool;
  val vars =
    P("var" ~ typed ~ ";")

  // local variables are declared at the beginning of a block, as in Dafny
  val block =
    Block(P(braces(vars.*.map(_.flatten) ~ prog.*)))

  // else if chains are nested if statements
  val else_block_or_skip =
    P(("else" ~ (if_ | block)) | R(Skip))

  // the guard * of a choice or of nondeterministic iterations
  val star = op("*")

  val guard =
    P(star.map(None) | some(expr))

  val if_ : Parser[Prog] =
    If(P("if" ~ parens(guard) ~ block ~ else_block_or_skip))

  val while_ =
    While(P("while" ~ parens(guard) ~ (invariant | modifies).* ~ block))

  val prog: Parser[Prog] =
    P(break | return_ | assume | assert | havoc | call | if_ | while_ | block | assign)

  // attributes of top-level commands
  val attr =
    Attr(P("{:" ~ id ~ (expr ~* ",") ~ "}"))

  val attrs =
    P(attr.*)

  // type parameters are in angle brackets, type array<a, b>, unlike in Boogie
  val sortdef =
    SortDef(P("type" ~ attrs ~ id ~ params ~ ("=" ~ typ).? ~ ";"))

  val constdef =
    ConstDef(P("const" ~ attrs ~ typed ~ ";"))

  val vardef =
    VarDef(P("var" ~ attrs ~ typed ~ ";"))

  val fundef =
    FunDef(P("function" ~ attrs ~ id ~ params ~ formals ~ ":" ~ typ ~ (some(braces(expr)) | (";" ~ none))))

  val axiom =
    Axiom(P("axiom" ~ attrs ~ expr ~ ";"))

  val lemma =
    Lemma(P("lemma" ~ attrs ~ expr ~ ";"))

  val returns =
    P(("returns" ~ formals) | nil)

  val spec =
    P(requires | ensures | modifies)

  // procedures without body end the signature with a semicolon, those with body must not
  val contract =
    P((";" ~ spec.* ~ none) | (spec.* ~ some(block)))

  val procdef =
    ProcDef(P("procedure" ~ attrs ~ id ~ params ~ formals ~ returns ~ contract))

  val cmd: Parser[Cmd] =
    P(sortdef | constdef | vardef | fundef | axiom | lemma | procdef)

  val script =
    P(cmd.*)
