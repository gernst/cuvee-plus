package cuvee

object Debug:
  // modules for which debug output is enabled, see command line option -debug
  var modules: Set[String] = Set()

  // the message is computed only if debugging is enabled for `what`
  def info(what: String, msg: => String) =
    if modules.contains(what)
    then System.err.println("[" + what + "] " + msg)

trait Debug:
  def apply(msg: String, info: Any*): Throwable

  def raise[A](msg: String, info: Any*) =
    throw apply(msg, info*)

  def report[A](msg: String, info: Any*)(f: => A): A =
    try f
    catch
      case cause: Throwable =>
        throw apply(msg, info*).initCause(cause)

case class Fatal(msg: String, info: Any*) extends Throwable:
  override def toString =
    "Fatal(" + msg + "," + info.mkString(",") + ")"

case class Error(msg: String, info: Any*) extends Throwable with core.Result:
  override def toString =
    "Error(" + msg + "," + info.mkString(",") + ")"

object Fatal extends Debug
object Error extends Debug
