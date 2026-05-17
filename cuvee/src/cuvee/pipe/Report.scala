package cuvee.pipe

import cuvee.smtlib._

trait Report:
  def report(result: Result): Unit
  def error(msg: String): Unit
