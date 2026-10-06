package cuvee.c

import scala.collection.mutable

import easyparse.Token

// the lexer hack of C: the grammar needs to know the names of types, which typedef defines,
// hence the scanner replaces them by the tokens of their definitions, e.g. size_t by unsigned int,
// and the grammar skips typedef declarations (see Grammar.typedef_);
// the name of a type is the last name of its definition, e.g. typedef unsigned int size_t,
// other definitions, e.g. of arrays and of pointers to functions, define no names;
// the names are global, even if defined in a block
class Typedefs(scanner: cuvee.pipe.Scanner) extends cuvee.pipe.Scanner:
  val types = mutable.Map[String, List[Token]]()
  val pending = mutable.Queue[Token]()

  def next: Token =
    if pending.nonEmpty
    then pending.dequeue()
    else
      scanner.next match
        case Token.Keyword("typedef") =>
          val tokens = definition()

          tokens.reverse match
            case (Token.Keyword(";")) :: Token.Value("sym", name) :: rest if rest.nonEmpty =>
              types(name) = rest.reverse
            case _ =>

          pending ++= tokens
          Token.Keyword("typedef")

        case tok =>
          expand(tok)

  // the tokens of a name of a type defined before, otherwise the token itself
  def expand(tok: Token): Token =
    tok match
      case Token.Value("sym", name) if types.contains(name) =>
        val first :: rest = types(name): @unchecked
        pending ++= rest
        first

      case _ =>
        tok

  // the tokens up to the semicolon that ends the definition, outside of braces, e.g. typedef struct { int n; } S,
  // where names of types defined before are expanded
  def definition(): List[Token] =
    val tokens = mutable.ListBuffer[Token]()
    var depth = 0
    var done = false

    while !done
    do
      // the pending tokens of expansions are part of the definition
      val tok = if pending.nonEmpty then pending.dequeue() else expand(scanner.next)
      tokens += tok

      tok match
        case Token.Keyword("{") => depth += 1
        case Token.Keyword("}") => depth -= 1
        case Token.Keyword(";") => done = depth == 0
        case _                  => done = tok == Token.eof

    tokens.toList
