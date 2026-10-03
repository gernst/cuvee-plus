package cuvee.dafny

import cuvee.Name
import cuvee.core._
import cuvee.smtlib._

import easyprint.Doc
import easyprint.Doc.{text, line, linebreak, join, render}
import easyprint.Group
import easyprint.Nest

object Printer extends cuvee.pipe.Printer:
  // the width that documents are laid out for
  val width = 80

  // names of built-in sorts and functions in Dafny, inverse of the translation by the grammar
  val untranslate =
    Grammar.translate.map(_.swap)

  // indexed names are printed with the index as unicode subscript, e.g. a₃
  def name(name: Name): String =
    name match
      case Name(name, None) =>
        untranslate.getOrElse(name, name)

      case _ =>
        name.subscripted

  // elements separated by commas, which go on separate lines if the enclosing group does not fit
  def commas(docs: List[Doc]): Doc =
    join(docs, text(",") ++ line)

  def lines(res: Result) = ???
  def lines(cmd: Cmd) = ???

  def lines(typ: Type): List[String] =
    render(doc(typ), width)

  def lines(expr: Expr): List[String] =
    render(doc(expr), width)

  def lines(prog: Prog) = ???

  // types are not broken across lines
  def doc(typ: Type): Doc =
    typ match
      case Param(name_) =>
        text(name(name_))

      case Sort(Con(name_, _), Nil) =>
        text(name(name_))

      case Sort(Con(name_, _), args) =>
        text(name(name_)) ++ text("<") ++ join(args.map(doc(_)), text(", ")) ++ text(">")

  def formals(vars: List[Var]): Doc =
    val formals_ =
      for Var(name_, typ) <- vars
      yield text(name(name_) + ": ") ++ doc(typ)

    commas(formals_)

  // operators are still printed like function calls until mixfix printing is done
  def doc(expr: Expr): Doc =
    expr match
      case Var(name_, _) =>
        text(name(name_))

      case Lit(value: BigInt, _) =>
        text(value.toString)

      case Lit(value: String, _) =>
        text("\"" + value + "\"")

      case Lit(value, _) =>
        cuvee.Error.raise("unprintable literal", expr)

      case Ite(test, left, right) =>
        Group(text("if ") ++ doc(test) ++ line ++ text("then ") ++ doc(left) ++ line ++ text("else ") ++ doc(right))

      case Select(base, index) =>
        doc(base) ++ text("[") ++ doc(index) ++ text("]")

      case Store(base, index, value) =>
        Group(doc(base) ++ text("[") ++ Nest(2, linebreak ++ doc(index) ++ text(" :=") ++ line ++ doc(value)) ++ text("]"))

      case App(fun, _, _, Nil) =>
        text(name(fun.name))

      case App(fun, _, _, args) =>
        Group(text(name(fun.name) + "(") ++ Nest(2, linebreak ++ commas(args.map(doc(_)))) ++ text(")"))

      case Bind(quant, bound, body) =>
        Group(text(name(quant) + " ") ++ Group(formals(bound)) ++ text(" ::") ++ Nest(2, line ++ doc(body)))

      case Let(bound, args, body) =>
        val names = commas(bound.map(x => text(name(x.name))))
        Group(text("var ") ++ names ++ text(" := ") ++ commas(args.map(doc(_))) ++ text(";") ++ line ++ doc(body))
