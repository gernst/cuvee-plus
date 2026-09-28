package cuvee.test

import util.Main
import cuvee.Cuvee

object Parsing extends Main with Tests:
  def main(args: Array[String]) =
    tests("parse examples"):
      val files = Tests.find("./examples", ".dfy")

      for file <- files
      do
        test(file):
          val (cmds, results) = Cuvee.run(file)
