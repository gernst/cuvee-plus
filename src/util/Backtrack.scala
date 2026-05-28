package util

import scala.annotation.targetName

case object Backtrack extends Throwable

def backtrack =
  throw Backtrack

extension [A](first: => A)
  infix def or[B <: A](second: => B) =
    try first
    catch
      case Backtrack =>
        second