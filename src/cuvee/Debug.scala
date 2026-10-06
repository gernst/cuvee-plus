package cuvee

object Debug:
  // modules for which debug output is enabled, see command line option -debug
  var modules: Set[String] = Set()

  // the message is computed only if debugging is enabled for `what`
  def info(what: String, msg: => String) =
    if modules.contains(what)
    then System.err.println("[" + what + "] " + msg)

  // a step from `before` to `after`, where ~> starts the second line,
  // such that both terms begin at the same column after the prefix [what]
  def step(what: String, before: => String, after: => String) =
    if modules.contains(what)
    then
      val prefix = "[" + what + "] "
      System.err.println(prefix + before + "\n" + " " * (prefix.length - 3) + "~> " + after)

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
object Error extends Debug:
  // the error itself, not just a Throwable, so it can also be reported as a result
  override def apply(msg: String, info: Any*): Error =
    new Error(msg, info*)
