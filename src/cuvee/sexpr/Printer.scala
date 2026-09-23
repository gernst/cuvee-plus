package cuvee.sexpr

import cuvee.Name
import java.util.regex.Pattern

object Printer:
  def lines(expr: Any): List[String] =
    expr match
      case Id(text)      => atom(escape(text))
      case expr: Atom    => atom(expr.text)
      case args: List[_] => list(args flatMap lines)

  def atom(text: String) =
    List(text)

  val simple =
    Pattern.compile("[:]?[a-zA-Z_~!@$%^&*+=<>.?/\\-][0-9a-zA-Z_~!@$%^&*+=<>.?/\\-]*")

  def escape(str: String) =
    if simple.matcher(str).matches()
    then str
    else "|" + str + "|"

  def list(args: List[String]): List[String] =
    args match
      case Nil =>
        List("()")

      case first :: rest =>
        val max = args.maxBy(_.length)
        val sum = args.foldLeft(0)(_ + _.length)
        val brk = args.length >= 2 && (max.length > 20 || sum >= 80)

        brk match
          case true =>
            ("(" + first) :: indent("  ", rest)
          case false =>
            List(args.mkString("(", " ", ")"))

  def indent(prefix: String, lines: List[String]): List[String] =
    lines match
      case Nil           => Nil
      case List(last)    => List(prefix + last + ")")
      case first :: rest => (prefix + first) :: indent(prefix, rest)
