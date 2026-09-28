package cuvee.smtlib

import java.io.Reader

import cuvee.core.Cmd
import cuvee.pipe.Scanner

object Source extends cuvee.pipe.Source {

  def newScanner(reader: Reader): Scanner = ???

  def newParser(): easyparse.Parser[List[Cmd]] = ???
}
