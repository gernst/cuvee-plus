package cuvee.test

import java.io.File
import scala.util.DynamicVariable

import cuvee.Error

object Check:
  case class NotTrue(msg: String) extends Throwable:
    override def toString =
      "not true: " + msg

  case class NotEqual[A](msg: String, actual: A, expected: A) extends Throwable:
    override def toString =
      "not equal: " + msg + "\n    actual:   " + actual + "\n    expected: " + expected

  def that(msg: String, phi: Boolean) =
    if !phi
    then throw NotTrue(msg)

  def equal[A](msg: String, actual: A, expected: A) =
    if actual != expected
    then throw NotEqual(msg, actual, expected)

  // `action` must raise an error with message `msg`
  def fails(msg: String)(action: => Any) =
    val actual =
      try
        action
        None
      catch
        case error: Error =>
          Some(error.msg)

    equal("error", actual, Some(msg))

trait Tests:
  object indent extends DynamicVariable("")

  def tests(msg: String)(action: => Any) =
    println(indent.value + msg)
    indent.withValue(indent.value + "  "):
      action
    println()

  def test(msg: String)(action: => Any) =
    try
      print(indent.value + msg + " ...")
      action
      println(" passed")

    catch
      case e =>
        println(" failed")
        println("  " + e)

object Tests:
  def find(dir: String, suffix: String, exclude: List[String] = Nil): List[String] =
    for file <- find(new File(dir), suffix, exclude)
    yield file.getPath()

  def find(dir: File, suffix: String, exclude: List[String]): List[File] =
    Error.report("test directory not found", dir):
      require(dir.isDirectory)

    dir.listFiles.toList.flatMap:
      case file if file.getName.endsWith(suffix) =>
        List(file)

      case file if exclude.contains(file.getName) =>
        Nil

      case file if file.isDirectory =>
        find(file, suffix, exclude)

      case _ =>
        Nil
