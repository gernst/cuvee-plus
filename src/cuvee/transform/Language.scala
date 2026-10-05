package cuvee.transform

import cuvee.core._
import cuvee.pipe.Sink

// the implicit last step of each run, which drops the declarations that are part of the language of the output:
// those of the preludes (resources/cuvee/*/prelude.*) name the languages that they are part of by attributes,
// the file extensions smt2, dfy, bpl, and c, e.g. the tuples of Dafny are part of Dafny only,
// and are therefore declared as datatypes in SMT-LIB;
// it filters the commands in front of the sink one by one, unlike a stage, which buffers declarations,
// such that the answers of the sink to the remaining declarations are reported, e.g. unsupported by solvers
object Language:
  case class sink(language: String, next: Sink) extends Sink:
    def query(cmd: Cmd) =
      if isPart(language, cmd)
      then (Ack.Success, this)
      else
        val (result, next_) = next.query(cmd)
        (result, copy(next = next_))

  // whether `cmd` is a declaration that is part of `language`
  def isPart(language: String, cmd: Cmd): Boolean =
    attrs(cmd).exists(_.attrs.exists(_._1 == language))

  def attrs(cmd: Cmd): Option[Attrs] =
    cmd match
      case DeclareSort(_, attrs)         => Some(attrs)
      case DefineSort(_, _, _, attrs)    => Some(attrs)
      case DeclareDatatypes(_, _, attrs) => Some(attrs)
      case DeclareFun(_, attrs)          => Some(attrs)
      case DefineFun(_, _, attrs)        => Some(attrs)
      case _                             => None
