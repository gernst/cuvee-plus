package cuvee.c

import java.io.Reader

// C starts from the state of the SMT-LIB prelude, the parser builds expressions on Int and Bool directly,
// hence no overloaded operators remain to be resolved;
// the whole translation unit is parsed at once, such that the modified global variables can be inferred
object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    new Scanner(reader)

  def newParser() =
    val (init, _) = cuvee.smtlib.Source.newParser()
    val parser = new Parser(init)
    val lifted = Grammar.unit.map(parser.resolve)
    (init, lifted)
