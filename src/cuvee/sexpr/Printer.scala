package cuvee.sexpr

import util.Name
import java.util.regex.Pattern

object Printer:
  def lines(expr: Any): List[String] =
    expr match
      case Id(text)      => atom(escape(text))
      case Kw(text)      => atom(":" + text)
      case Str(text)     => atom(str(text))
      case Hex(text)     => atom("#x" + text)
      case Bin(text)     => atom("#b" + text)
      case expr: Atom    => atom(expr.text)
      case args: List[_] => list(flat(args))

  def flat(args: List[Any]) =
    args flatMap lines

  def atom(text: String) =
    List(text)

  val simple =
    Pattern.compile("[:]?[a-zA-Z_~!@$%^&*+=<>.?/\\-][0-9a-zA-Z_~!@$%^&*+=<>.?/\\-]*")

  def escape(str: String) =
    if simple.matcher(str).matches()
    then str
    else "|" + str + "|"

  // SMT-LIB 2.6 escapes double quotes in string literals by doubling them
  def str(text: String) =
    "\"" + text.replace("\"", "\"\"") + "\""

  // the width beyond which lists are broken into lines, set by -linewidth (see Config)
  var width = 80

  def list(args: List[String]): List[String] =
    args match
      case Nil =>
        List("()")

      case first :: rest =>
        val max = args.maxBy(_.length)
        val sum = args.foldLeft(0)(_ + _.length)
        val brk = args.length >= 2 && (max.length > 20 || sum >= width)

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
