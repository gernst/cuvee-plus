package cuvee.test

import java.io.File

object Assert:
  case class NotTrue(msg: String) extends Throwable
  case class NotEqual[A](msg: String, actual: A, expected: A) extends Throwable

  def that(msg: String, phi: Boolean) =
    if !phi
    then throw NotTrue(msg)

  def equals[A](msg: String, actual: A, expected: A) =
    if actual != expected
    then throw NotEqual(msg, actual, expected)

trait Tests:
  def tests(msg: String)(action: => Any) =
    println(msg)
    action
    println()

  def test(msg: String)(action: => Any) =
    try
      print(msg + " ... ")
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
    dir.listFiles.toList.flatMap:
      case file if file.getName.endsWith(suffix) =>
        List(file)

      case file if exclude.contains(file.getName) =>
        Nil

      case file if file.isDirectory =>
        find(file, suffix, exclude)

      case _ =>
        Nil
