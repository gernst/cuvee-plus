package cuvee.test

import java.io.File
import scala.io.Source

import util.Main
import cuvee.Cuvee
import cuvee.Error

object Parsing extends Main with Tests:
  def main(args: Array[String]) =
    tests("parse examples"):
      val files = Tests.find("./examples", ".dfy")

      for file <- files
      do
        test(file):
          val (cmds, results) = Cuvee.run("-print", "null", file)

    // SMT-LIB examples must parse without errors,
    // and printing must be stable when the output is parsed again
    tests("parse smtlib examples"):
      val files = Tests.find("./examples", ".smt2")

      for file <- files
      do
        test(file):
          val (cmds, results) = Cuvee.run("-print", "null", file)
          val errors = results.collect { case error: Error => error.msg }
          Check.equal("errors", errors, Nil)

          val first = File.createTempFile("cuvee", ".smt2")
          val second = File.createTempFile("cuvee", ".smt2")
          first.deleteOnExit()
          second.deleteOnExit()

          Cuvee.run(file, "-o", first.getPath)
          Cuvee.run(first.getPath, "-o", second.getPath)
          Check.equal("round trip", read(second), read(first))

  def read(file: File) =
    val source = Source.fromFile(file)
    try source.mkString
    finally source.close()
