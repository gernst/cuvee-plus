package util

import scala.util.control.NoStackTrace

// control flow only, a stack trace would be meaningless since there is a single instance
case object Backtrack extends Throwable with NoStackTrace

def backtrack =
  throw Backtrack

extension [A](first: => A)
  infix def or[B <: A](second: => B) =
    try first
    catch
      case Backtrack =>
        second