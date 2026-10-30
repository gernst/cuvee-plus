package cuvee.boogie

import util.Name
import cuvee.Error

object Grammar:
  import easyparse._
  import Brackets._

  val prefix_ops = Map(
    "-" -> 8,
    "!" -> 8
  )

  val postfix_ops = Map[String, Int]()

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

  val subscripted = "(.+?)([₀-₉]+)".r

  def index(name: String) =
    name match
      case subscripted(base, digits) =>
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
  val attr_ = T("attr")

  // const names constant arrays, too, e.g. in the prelude of C
  // keywords that remain identifiers elsewhere
  val op = P(sym | J("<") | J(">") | J("*") | J("const") | J("annotate") | J("verify")
    | J("logic") | J("option") | J("info") | J("witness") | J("labels") | J("model") | J("exit") | J("push") | J("pop") | J("reset"))
  val id = Sym(op)

  val nil = R(Nil)
  val none = R(None)
  val true_ = R(True: Expr)
  val skip = R(Skip)

  def some[A](p: Parser[A]) =
    p.map { Some(_) }

  def list[A](p: Parser[A]) =
    p.map { List(_) }

  def angle[A](p: Parser[A]) =
    "<" ~ p ~ ">"

  val ids =
    P(id ~+ ",")

  val exprs =
    P(expr ~+ ",")

  val params =
    P(angle(ids) | nil)

  val array =
    Array(P(brackets(types) ~ typ))

  val types =
    P(typ ~+ ",")

  val sort =
    Sort(P(id ~ (angle(types) | nil)))

  val typ: Parser[Type] =
    P(array | parens(typ) | sort)

  val typed =
    P((ids ~ ":" ~ typ) ~+ ",")

  val formals =
    P(parens(typed | nil))

  val args =
    P(parens(expr ~* ","))

  val lit =
    P(Num(num) | Dec(dec) | Str(str))

  // .i scans as a symbol, since the dot is a character of identifiers
  val component = "\\.([0-9]+)".r

  val access: Parser[Selector] =
    P(Access(P(brackets(exprs ~ (":=" ~ expr).?))) | Member(sym.collect { case component(i) => i.toInt }))

  val app =
    App(P(id ~ (args | nil)))

  val trigger =
    P(braces(exprs))

  val binding =
    P(typed ~ "::" ~ trigger.* ~ expr)

  val forall =
    All(P("forall" ~ binding))

  val exists =
    Ex(P("exists" ~ binding))

  // a map of a single index, written (lambda x: T :: e)
  val lambda =
    Lam(P("lambda" ~ typed ~ "::" ~ expr))

  val parenthesized =
    P("(" ~ (forall | exists | lambda | expr) ~ ")")

  val ite =
    Ite(P("if" ~ expr ~ "then" ~ expr ~ "else" ~ expr))

  // guarded cases case p => x case q => y, or a single result
  val guarded =
    P("case" ~ expr ~ "=>" ~ expr)

  val update: Parser[List[(Expr, Expr)]] =
    P(guarded.+ | list(true_ ~ expr))

  // the results of the accumulators of a trace, separated by commas, each guarded cases or a plain expression
  val updates: Parser[List[List[(Expr, Expr)]]] =
    P(update ~+ ",")

  // the initial values each end with a comma, since a list separated by commas would commit to an expression after
  // the comma before the keyword for (as in Dafny)
  val inits: Parser[List[Expr]] =
    P((expr ~ ",").+)

  val trace_ =
    Combinator(P(J("trace") ~ "(" ~ inits ~ "for" ~ exprs ~ "do" ~ ids ~ "::" ~ updates ~ ")"))

  val map_ =
    Combinator(P(J("map") ~ nil ~ "(" ~ "for" ~ exprs ~ "yield" ~ ids ~ "::" ~ list(update) ~ ")"))

  val all_ =
    Combinator(P(J("all") ~ nil ~ "(" ~ "for" ~ exprs ~ "check" ~ ids ~ "::" ~ list(list(true_ ~ expr)) ~ ")"))

  val combinator =
    P(trace_ | map_ | all_)

  val butlast =
    Butlast(P("⌊" ~ expr ~ "⌋"))

  val atom: Parser[Expr] =
    P(lit | parenthesized | ite | butlast | combinator | app)

  val inner: Parser[Expr] =
    Inner(P(atom ~ access.*))

  val expr: Parser[Expr] =
    M(op, prefix_ops, postfix_ops, infix_ops) $ (inner, (op, args) => App(Sym(op), args))

  val requires =
    Requires(P("requires" ~ expr ~ ";"))

  val ensures =
    Ensures(P("ensures" ~ expr ~ ";"))

  val invariant =
    Invariant(P("invariant" ~ expr ~ ";"))

  val modifies =
    Modifies(P("modifies" ~ ids ~ ";"))

  val decreases =
    Decreases(P("decreases" ~ exprs ~ ";"))

  val break =
    Break("break" ~ ";")

  val continue_ =
    Continue("continue" ~ ";")

  val return_ =
    Return("return" ~ ";")

  val assume =
    Assume(P("assume" ~ expr ~ ";"))

  val assert =
    Assert(P("assert" ~ expr ~ ";"))

  val havoc =
    Havoc(P("havoc" ~ ids ~ ";"))

  val call =
    Call(P("call" ~ ((ids ?~ ":=") | nil) ~ id ~ args ~ ";"))

  val lhs =
    Lhs(P(id ~ brackets(exprs).*))

  val assign =
    Assign(P((lhs ~+ ",") ~ ":=" ~ exprs ~ ";"))

  val local =
    Local(P("var" ~ typed ~ ";"))

  val block =
    Block(P(braces(local.* ~ prog.*)))

  val else_or_skip =
    P(("else" ~ (if_ | block)) | skip)

  val guard =
    P("*".map(None) | some(expr))

  val if_ : Parser[Prog] =
    If(P("if" ~ parens(guard) ~ block ~ else_or_skip))

  val while_ =
    While(P("while" ~ attrs ~ parens(guard) ~ (invariant | modifies | decreases).* ~ block))

  val annotated =
    Annotated(P(attr.+ ~ block))

  val prog: Parser[Prog] =
    P(break | continue_ | return_ | assume | assert | havoc | call | if_ | while_ | annotated | block | assign)

  // {:name is a token of its own, such that a block that follows attributes is not taken for another attribute
  val attr =
    Attr(P(attr_ ~ (expr ~* ",") ~ "}"))

  val attrs =
    P(attr.*)

  val sortdef =
    SortDef(P("type" ~ attrs ~ id ~ params ~ ("=" ~ typ).? ~ ";"))

  val sel =
    Sel(P(id ~ ":" ~ typ))

  val sels =
    P(parens(sel ~* ",") | nil)

  val constr =
    Constr(P(id ~ sels))

  val data =
    Data(P(id ~ params ~ "=" ~ (constr ~+ "|")))

  val datadef =
    DataDef(P("data" ~ attrs ~ (data ~+ "and") ~ ";"))

  val constdef =
    ConstDef(P("const" ~ attrs ~ typed ~ ";"))

  val vardef =
    VarDef(P("var" ~ attrs ~ typed ~ ";"))

  val fundef =
    FunDef(P("function" ~ attrs ~ id ~ params ~ formals ~ ":" ~ typ ~ (some(braces(expr)) | (";" ~ none))))

  val axiom =
    Axiom(P("axiom" ~ params ~ attrs ~ expr ~ ";"))

  val lemma =
    Lemma(P("lemma" ~ params ~ attrs ~ expr ~ ";"))

  val returns =
    P(("returns" ~ formals) | nil)

  val spec =
    P(requires | ensures | modifies | decreases)

  val contract =
    P((";" ~ spec.* ~ none) | (spec.* ~ some(block)))

  val procdef =
    ProcDef(P("procedure" ~ attrs ~ id ~ params ~ formals ~ returns ~ contract))

  val annotate =
    Annotate(P("annotate" ~ str ~ attr.+ ~ ";"))

  val verify =
    Verify(P("verify" ~ id ~ args ~ ";"))

  val control =
    P(
      (((J("check") | J("labels") | J("model") | J("witness") | J("exit") | J("reset")) ~ R(None: Option[String])) |
        ((J("push") | J("pop")) ~ num.map(Some(_))) |
        (J("logic") ~ id.map(Some(_)))) ~ ";"
    ).map(Control(_, _))

  val setting =
    P((J("option") | J("info")) ~ attr ~ ";").map(Setting(_, _))

  val cmd: Parser[Cmd] =
    P(sortdef | datadef | constdef | vardef | fundef | axiom | lemma | procdef | annotate | verify | control | setting)

  val script =
    P(cmd.*)
