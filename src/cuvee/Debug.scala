package cuvee

object Debug:
  def info(what: String, msg: String) =
    ???

case class Fatal(msg: String) extends Throwable:
  override def toString =
    "Fatal(" + msg + ")"

object Error:
  def report(msg: String) =
    throw cuvee.core.Error(msg)

  def reportIf(msg: String, phi: Boolean) =
    if phi then report(msg)

  def abort(msg: String) =
    throw Fatal(msg)

  def abortIf(msg: String, phi: Boolean) =
    if phi then abort(msg)