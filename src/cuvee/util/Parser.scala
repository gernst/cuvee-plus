package cuvee.util

import scala.annotation.tailrec

type Text = List[Tok]

def ^(arg: Any) =
  Pat.Ret(arg)

def $(pats: Pat*): Pat.Seq =
  Pat.Seq(pats.toList)

def $(res: Res*) =
  Res.Seq(res.toList)

def v(label: String) =
  Pat.Val(label)

def a(pats: Pat*) =
  Pat.Alt(pats.toList)

def p(pat: => Pat) =
  Pat.Rec(() => pat)

extension (pat: Pat.Seq)
  infix def ~>(res: Res) =
    Pat.Rule(pat.pats, res)

implicit def PatLit(text: String): Pat =
  Pat.Lit(text)

implicit def ResLit(text: String): Res =
  Res.Lit(text)

implicit def ResVal(pos: Int): Res =
  Res.Val(pos)

enum Tok:
  case Lit(text: String)
  case Val(label: String, value: Any)

enum Pat:
  case Ret(arg: Any)
  case Lit(text: String)
  case Val(label: String)
  case Seq(pats: List[Pat])
  case Alt(alt: List[Pat])
  case Rec(from: () => Pat)
  case Rule(pats: List[Pat], res: Res)

enum Res:
  case All
  case Lit(text: String)
  case Val(pos: Int)
  case Seq(res: List[Res])

object Pat:
  object Backtrack extends Throwable:
    override def fillInStackTrace() = this

  case class Fail(in: Text, pats: List[Pat]) extends Exception

  def fail(in: Text, pats: List[Pat], cm: Boolean) =
    if cm
    then throw Fail(in, pats)
    else throw Backtrack

  def parse(in: Text, pats: List[Pat], cm: Boolean): (List[Any], Text) =
    (in, pats) match
      case (_, Nil) =>
        (Nil, in)

      case (_, Pat.Ret(arg) :: rest) =>
        val (args_, in_) = parse(in, rest, true)
        (arg :: args_, in_)

      case (_, Pat.Rec(from) :: rest) =>
        parse(in, from() :: rest, cm)

      case (Tok.Lit(text) :: in_, Pat.Lit(text_) :: rest) if text == text_ =>
        parse(in_, rest, true)

      case (Tok.Val(label, arg) :: in_, Pat.Val(label_) :: rest) if label == label_ =>
        val (args_, in__) = parse(in_, rest, true)
        (arg :: args_, in__)

      case (_, Pat.Alt(pats) :: rest) =>
        choose(in, pats, rest, cm)

      case (_, Pat.Seq(pats) :: rest) =>
        val (arg, in_) = parse(in, pats, true)
        val (args_, in__) = parse(in_, rest, true)
        (arg :: args_, in__)

      case (_, Pat.Rule(pats, res) :: rest) =>
        val (args, in_) = parse(in, pats, true)
        val arg = Res.reduce(args, res)
        val (args_, in__) = parse(in_, rest, true)
        (arg :: args_, in__)

      case _ =>
        fail(in, pats, cm)

  @tailrec
  def choose(in: Text, pats: List[Pat], rest: List[Pat], cm: Boolean): (List[Any], Text) =
    pats match
      case Nil =>
        fail(in, pats, cm)

      case pat :: alt =>
        try parse(in, pat :: rest, false)
        catch
          case Backtrack =>
            choose(in, alt, rest, cm)

object Res:
  def reduce(args: List[Any], res: Res): Any =
    res match
      case All =>
        args

      case Lit(text) =>
        text

      case Val(pos) =>
        args(pos)

      case Seq(pats) =>
        for res <- pats
        yield reduce(args, res)
