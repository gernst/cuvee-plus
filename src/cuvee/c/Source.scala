package cuvee.c

import java.io.Reader

import cuvee.Config

// C starts from the state and the declarations of the SMT-LIB prelude, the parser builds expressions on Int and Bool directly,
// hence no overloaded operators remain to be resolved;
// the whole translation unit is parsed at once, such that the modified global variables can be inferred
object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    new Typedefs(new Scanner(reader))

  // the translation unit is resolved for the data model of the configuration
  def newParser(config: Config) =
    val (init, _, prelude) = cuvee.smtlib.Source.newParser(config)
    val parser = new Parser(init, config.arch)
    (init, Grammar.unit.map(parser.resolve), prelude)
