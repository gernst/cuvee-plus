package cuvee

case class Fatal(msg: String) extends Throwable

object Error:
  def report(msg: String) =
    throw cuvee.smtlib.Error(msg)

  def reportIf(msg: String, phi: Boolean) =
    if phi then report(msg)

  def abort(msg: String) =
    throw Fatal(msg)

  def abortIf(msg: String, phi: Boolean) =
    if phi then abort(msg)

@main
def run() = {
  ???
}
