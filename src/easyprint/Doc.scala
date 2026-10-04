package easyprint

import scala.collection.mutable

// documents for pretty printing, after Wadler, "A prettier printer":
// a group is laid out on a single line if it fits into the remaining width,
// otherwise its line breaks become newlines, indented by the enclosing nesting
sealed trait Doc:
  infix def ++(that: Doc): Doc =
    Concat(this, that)

  // concatenation with a space in between
  infix def +:+(that: Doc): Doc =
    this ++ Doc.space ++ that

case class Text(text: String) extends Doc
// `flat` is printed instead of the newline when laid out flat, a hard line has no flat alternative
case class Line(flat: Option[String]) extends Doc
case class Nest(indent: Int, doc: Doc) extends Doc
// the newlines inside are indented to the column at which the document starts
case class Align(doc: Doc) extends Doc
case class Concat(left: Doc, right: Doc) extends Doc
case class Group(doc: Doc) extends Doc

object Doc:
  given Conversion[String, Doc] =
    text(_)

  val empty: Doc = Text("")
  val space: Doc = Text(" ")

  def text(text: String): Doc =
    Text(text)

  // a space, or a newline if the enclosing group does not fit
  val line: Doc = Line(Some(" "))

  // nothing, or a newline if the enclosing group does not fit
  val linebreak: Doc = Line(Some(""))

  // always a newline, the enclosing groups are never laid out flat
  val hardline: Doc = Line(None)

  def concat(docs: Iterable[Doc]): Doc =
    docs.foldLeft(empty)(_ ++ _)

  // docs with `sep` in between
  def join(docs: Iterable[Doc], sep: Doc): Doc =
    if docs.isEmpty
    then empty
    else docs.reduceLeft(_ ++ sep ++ _)

  // lines that are already laid out, e.g. by another printer, separated by hard lines
  def lines(lines: Iterable[String]): Doc =
    join(lines.map(text), hardline)

  // layout mode of a pending document
  case class Item(indent: Int, flat: Boolean, doc: Doc)

  def render(doc: Doc, width: Int): List[String] =
    val lines = mutable.ListBuffer[String]()
    val line = new StringBuilder()

    def newline(indent: Int) =
      lines += line.toString.stripTrailing
      line.clear()
      line ++= " " * indent

    var todo = List(Item(0, false, doc))

    while todo.nonEmpty do
      val item = todo.head
      todo = todo.tail

      item.doc match
        case Text(text) =>
          line ++= text

        case Line(Some(flat)) if item.flat =>
          line ++= flat

        case Line(_) =>
          newline(item.indent)

        case Nest(indent, doc) =>
          todo = Item(item.indent + indent, item.flat, doc) :: todo

        case Align(doc) =>
          todo = Item(line.length, item.flat, doc) :: todo

        case Concat(left, right) =>
          todo = Item(item.indent, item.flat, left) :: Item(item.indent, item.flat, right) :: todo

        case Group(doc) if item.flat =>
          todo = Item(item.indent, true, doc) :: todo

        case Group(doc) =>
          val flat = fits(width - line.length, Item(item.indent, true, doc) :: todo)
          todo = Item(item.indent, flat, doc) :: todo

    lines += line.toString.stripTrailing
    lines.toList

  // whether the text up to the next newline fits into `width`,
  // a hard line in a group that is laid out flat never fits
  def fits(width: Int, items: List[Item]): Boolean =
    var rest = width
    var todo = items

    while rest >= 0 && todo.nonEmpty do
      val item = todo.head
      todo = todo.tail

      item.doc match
        case Text(text) =>
          rest -= text.length

        case Line(Some(flat)) if item.flat =>
          rest -= flat.length

        case Line(None) if item.flat =>
          return false

        case Line(_) =>
          return true

        case Nest(indent, doc) =>
          todo = Item(item.indent + indent, item.flat, doc) :: todo

        case Align(doc) =>
          todo = Item(item.indent, item.flat, doc) :: todo

        case Concat(left, right) =>
          todo = Item(item.indent, item.flat, left) :: Item(item.indent, item.flat, right) :: todo

        case Group(doc) =>
          todo = Item(item.indent, item.flat, doc) :: todo

    rest >= 0
