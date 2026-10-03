package util

case class Name(name: String, index: Option[Int]):
  def withIndex(index: Int) =
    Name(name, Some(index))

  // the name with the index as unicode subscript, e.g. a₃
  def subscripted: String =
    index match
      case None =>
        name

      case Some(index) =>
        name + index.toString.map(digit => Name.subscripts(digit - '0'))

object Name:
  // subscript digits 0 to 9, indexed by the digit
  val subscripts = "₀₁₂₃₄₅₆₇₈₉"

  // inverse of how names are printed: a suffix $i denotes the index i
  val indexed = "(.+)\\$([0-9]+)".r

  given Conversion[String, Name] =
    case indexed(name, index) => Name(name, Some(index.toInt))
    case name                 => Name(name, None)
