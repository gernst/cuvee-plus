package cuvee.pipe

import cuvee.Error
import cuvee.core._

type Source = Iterable[Cmd]

trait Grammar:
  def init: State
  def cmd: easyparse.Parser[Any]

object Source:
  def read(scanner: Scanner, grammar: Grammar): Source =
    val in = scanner.input
    val parser = Parser(grammar.init)

    def cmds(in: easyparse.Input): LazyList[Cmd] =
      if in.isEmpty || in.head == null
      then LazyList.empty
      else
        try
          val (from, in_) = grammar.cmd.parse(in, true)
          val cmd = parser.cmd(from)
          cmd #:: cmds(in_)
        catch
          case easyparse.Fail(in, from) =>
            Error.raise("parse error", from, in)

    cmds(in)
