package cuvee.transform

import cuvee.core._
import cuvee.pipe.Sink

// the last step in front of each sink, which drops the declarations that its receiver knows by their features:
// those of the preludes (resources/cuvee/*/prelude.*) name the languages that they are part of by attributes,
// the file extensions smt2, dfy, bpl, and c, e.g. the tuples of Dafny are part of Dafny only,
// and are therefore declared as datatypes in SMT-LIB;
// it filters the commands in front of the sink one by one, unlike a stage, which buffers declarations,
// such that the answers of the sink to the remaining declarations are reported, e.g. unsupported by solvers
object Language:
  case class sink(features: Set[String], next: Sink) extends Sink:
    def query(cmd: Cmd) =
      if isPart(features, cmd)
      then (Ack.Success, Nil, this)
      else
        val (result, added, next_) = next.query(cmd)
        (result, added, copy(next = next_))

  // whether `cmd` is a declaration that has one of `features`
  def isPart(features: Set[String], cmd: Cmd): Boolean =
    cmd match
      case decl: Decl => features.exists(decl.attrs.contains)
      case _          => false
