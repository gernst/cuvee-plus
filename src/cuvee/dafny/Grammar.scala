package cuvee.dafny

import cuvee.Error

object Grammar:
  import easyparse._
  import Brackets._

  val prefix_ops = Map(
    "-" -> 9,
    "!" -> 9
  )

  val postfix_ops = Map[String, Int](
  )

  val infix_ops = Map(
    "<==>" -> (Assoc.Non, 0),
    "==>" -> (Assoc.Right, 1),
    "||" -> (Assoc.Left, 2),
    "&&" -> (Assoc.Left, 3),
    "==" -> (Assoc.Left, 5),
    "!=" -> (Assoc.Left, 5),
    ">=" -> (Assoc.Left, 5),
    ">" -> (Assoc.Left, 5),
    "<" -> (Assoc.Left, 5),
    "<=" -> (Assoc.Left, 5),
    "in" -> (Assoc.Non, 5),
    "!in" -> (Assoc.Non, 5),
    "+" -> (Assoc.Left, 6),
    "-" -> (Assoc.Left, 6),
    "*" -> (Assoc.Left, 7),
    "/" -> (Assoc.Left, 7),
    "%" -> (Assoc.Left, 7),
    // bitwise operators bind stronger than multiplication, as in Dafny
    "&" -> (Assoc.Left, 8),
    "^" -> (Assoc.Left, 8)
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
    "string" -> "String",
    "seq" -> "Seq",
    "set" -> "Set",
    "multiset" -> "Bag",
    "map" -> "Map",
    "array" -> "Array"
  )

  val avoid =
    translate.values.toSet

  val chainable = Set("==", "<", "<=", ">", ">=")

  def app(op: String, args: List[Expr]): Expr =
    App(Sym(op), args)

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

  val op = P(sym | J("<") | J(">") | J("==") | J("*") | J("map") | J("multiset"))
  val id = Sym(op)

  val id_prime = id ~ "'"

  val nil = R(Nil)
  val none = R(None)
  val true_ = R(True: Expr)
  val skip = R(Skip)

  def some[A](p: Parser[A]) =
    p.map { Some(_) }

  def list[A](p: Parser[A]) =
    p.map { List(_) }

  def left[A](p: Parser[A]) =
    p.map { Left(_) }

  def right[A](p: Parser[A]) =
    p.map { Right(_) }

  def angle[A](p: Parser[A]) =
    "<" ~ p ~ ">"

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

  val elems =
    P(expr ~* ",")

  val vars =
    P(formal ~+ ",")

  val params =
    P(angle(ids) | nil)

  val inst =
    P(angle(types) | nil)

  val sort =
    Sort(P(id ~ inst))

  val product =
    Product(P(parens(types)))

  val typ: Parser[Type] =
    P(product | sort)

  val formal =
    P(id ~ ":" ~ typ)

  val formals =
    P(parens(formal ~* ","))

  val args =
    P(parens(elems) | nil)

  val array =
    Array(P(brackets(expr.? ~ suffix.?)))

  val member =
    Member(P("." ~ (id | num) ~ args))

  val store =
    Store(P(":=" ~ expr))

  val upto =
    Upto(P(".." ~ expr.?))

  val suffix =
    P(store | upto)

  val as =
    As(P("as" ~ typ))

  val access =
    P(array | member | as)

  val app =
    App(P(id ~ args))

  val bool =
    R(Sort("Bool", Nil))

  val ite =
    Ite(P("if" ~ expr ~ "then" ~ expr ~ (("else" ~ expr) | true_)))

  val pat: Parser[Expr] =
    App(P(id ~ (parens(pat ~* ",") | nil)))

  val case_ =
    P("case" ~ pat ~ "=>" ~ expr)

  val match_ =
    Match(P("match" ~ expr ~ (braces(case_.+) | case_.+)))

  val bound =
    P(formals | vars)

  val forall =
    All(P("forall" ~ bound ~ "::" ~ expr))

  val exists =
    Ex(P("exists" ~ bound ~ "::" ~ expr))

  val bind =
    P(forall | exists)

  val let =
    Let(P("var" ~ vars ~ ":=" ~ exprs ~ ";" ~ expr))

  val tuple =
    Tuple(P(parens(exprs)))

  val diff =
    Diff(P(("(" ?~ ids ?~ "::") ~ expr ~ ")" ~ "'"))

  val seq =
    SeqLit(P(brackets(elems)))

  val len =
    Len(P("|" ~ expr ~ "|"))

  val set =
    SetLit(P(braces(elems)))

  val bag =
    BagLit(P("multiset" ~ "{" ~ elems ~ "}"))

  val map =
    MapLit(P("map" ~ "[" ~ ((expr ~ ":=" ~ expr) ~* ",") ~ "]"))

  val butlast =
    Butlast(P("⌊" ~ expr ~ "⌋"))

  val atom: Parser[Expr] =
    P(diff | tuple | seq | set | bag | map | len | butlast | lit | bind | let | ite | match_ | combinator | app)

  val inner: Parser[Expr] =
    Inner(P(atom ~ access.*))

  // guarded cases case p => x case q => y, or a single result
  val guarded =
    P("case" ~ expr ~ "=>" ~ expr)

  val update: Parser[List[(Expr, Expr)]] =
    P(guarded.+ | list(true_ ~ expr))

  val trace_ =
    Combinator(P(J("trace") ~ "(" ~ some(expr) ~ "," ~ "for" ~ exprs ~ "do" ~ ids ~ "::" ~ update ~ ")"))

  val map_ =
    Combinator(P(J("maps") ~ none ~ "(" ~ "for" ~ exprs ~ "yield" ~ ids ~ "::" ~ update ~ ")"))

  val all_ =
    Combinator(P(J("invs") ~ none ~ "(" ~ "for" ~ exprs ~ "check" ~ ids ~ "::" ~ list(true_ ~ expr) ~ ")"))

  val combinator =
    P(trace_ | map_ | all_)

  val expr: Parser[Expr] =
    M(op, prefix_ops, postfix_ops, infix_ops) $ (inner, app)

  val invariant =
    P("invariant" ~ expr)

  val requires =
    P("requires" ~ expr)

  val ensures =
    P("ensures" ~ expr)

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
    Local(P("var" ~ vars ~ (":=" ~ exprs).? ~ ";"))

  val assign =
    Assign(P(ids ?~ ":=" ~ exprs ~ ";"))

  val call =
    Assign(P(nil ?~ list(inner) ~ ";"))

  val block =
    Block(P(braces(local.* ~ prog.*)))

  val else_or_skip =
    P(("else" ~ (if_ | block)) | skip)

  val guard =
    P("*".map(None) | some(expr))

  val if_ : Parser[Prog] =
    If(P("if" ~ guard ~ block ~ else_or_skip))

  val while_ =
    While(P("while" ~ guard ~ modifies.* ~ invariant.* ~ decreases.* ~ block))

  val ode =
    Ode(P("ode" ~ id ~ "::" ~ (id_prime ~+ ",") ~ "==" ~ exprs ~ ("while" ~ expr).? ~ invariant.* ~ ";"))

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

  val annotation =
    P(braces(":" ~ id))

  val sortdef =
    SortDef(P("type" ~ annotation.* ~ id ~ params ~ (right(braces(sortcmd.*)) | left(sortalias.?))))

  val datadef =
    DataDef(P("datatype" ~ annotation.* ~ id ~ params ~ "=" ~ constrs ~ sortimpl.?))

  val datadefs =
    DataDefs(P(datadef.+))

  val constdef =
    FunDef(P("const" ~ annotation.* ~ id ~ params ~ nil ~ ":" ~ typ ~ nil ~ nil ~ nil ~ (":=" ~ expr).?))

  val fundef =
    FunDef(P("function" ~ annotation.* ~ id ~ params ~ formals ~ ":" ~ typ ~ requires.* ~ ensures.* ~ decreases.* ~ braces(expr).?))

  val preddef =
    FunDef(P("predicate" ~ annotation.* ~ id ~ params ~ formals ~ bool ~ requires.* ~ ensures.* ~ decreases.* ~ braces(expr).?))

  val axiom =
    Axiom(P("axiom" ~ params ~ annotation.* ~ expr))

  val lemma =
    Lemma(P("lemma" ~ params ~ annotation.* ~ expr))

  val goal =
    Goal(P("goal" ~ params ~ annotation.* ~ expr))

  val vardef =
    VarDef(P("var" ~ vars ~ Scanner.Choice(";", Scanner.Accept)))

  val returns =
    P("returns" ~ formals)

  val assumes =
    P("assumes" ~ expr)

  val commits =
    P("commits" ~ expr)

  val procdef =
    MethodDef(P("method" ~ id ~ params ~ formals ~ returns.? ~ modifies.* ~ requires.* ~ ensures.* ~ assumes.* ~ commits.* ~ decreases.* ~ block.?))

  val check =
    Check("check")

  val cmd: Parser[Cmd] =
    P(datadefs | sortdef | constdef | fundef | preddef | procdef | axiom | lemma | goal | vardef | check)

  val script =
    P(cmd.*)
