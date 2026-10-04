package util

case class Name(name: String, index: Option[Int]):
  def withIndex(index: Int) =
    Name(name, Some(index))

  // the name of the derivative, x'
  def primed =
    Name(name + "'", index)

  // the name with the index as unicode subscript, e.g. a₃
  def subscripted: String =
    index match
      case None =>
        name

      case Some(index) =>
        name + index.toString.map(digit => Name.subscripts(digit - '0'))

  // the name with the index after `sep`, e.g. a_3 for C
  def suffixed(sep: String): String =
    index match
      case None =>
        name

      case Some(index) =>
        name + sep + index

  // the name with the index after $, e.g. a$3, as in SMT-LIB
  def indexed: String =
    suffixed("$")

object Name:
  // subscript digits 0 to 9, indexed by the digit
  val subscripts = "₀₁₂₃₄₅₆₇₈₉"

  // inverse of how names are printed: a suffix $i (SMT-LIB) or a unicode subscript (Dafny, Boogie) denotes the index i
  val indexed = "(.+)\\$([0-9]+)".r
  val subscripted = "(.+?)([₀-₉]+)".r

  given Conversion[String, Name] =
    case indexed(name, index)     => Name(name, Some(index.toInt))
    case subscripted(name, index) => Name(name, Some(index.map(digit => (digit - '₀').toString).mkString.toInt))
    case name                     => Name(name, None)
