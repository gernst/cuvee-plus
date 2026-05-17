package cuvee.test

object Assert:
  case class NotTrue(msg: String) extends Throwable
  case class NotEqual[A](msg: String, actual: A, expected: A) extends Throwable

  def that(msg: String, phi: Boolean) =
    if !phi then throw NotTrue(msg)

  def equals[A](msg: String, actual: A, expected: A) =
    if actual != expected then throw NotEqual(msg, actual, expected)

trait Tests:
  def test(msg: String)(action: => Any) =
    try
      print(msg + " ... ")
      action
      println(" passed")

    catch
      case e =>
        println(" failed")
        println("  " + e)
