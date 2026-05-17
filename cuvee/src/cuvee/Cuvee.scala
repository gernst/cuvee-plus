package cuvee

case class Fatal(msg: String) extends Throwable
case class Error(msg: String) extends Throwable

object Error:
  def report(msg: String) =
    throw Error(msg)

  def reportIf(msg: String, phi: Boolean) =
    if phi then throw Error(msg)

  def abort(msg: String) =
    throw Error(msg)

  def abortIf(msg: String, phi: Boolean) =
    if phi then throw Fatal(msg)

@main
def run() = {
  ???
}
