package cuvee.sexpr

import scala.annotation.nowarn

import cuvee.Name

object Printer extends cuvee.Printer:
  def lines(expr: Any): List[String] =
    expr match
      case atom: Atom    => List(atom.text)
      case args: List[_] => app(args.toList flatMap lines)

  def app(args: List[String]): List[String] =
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
