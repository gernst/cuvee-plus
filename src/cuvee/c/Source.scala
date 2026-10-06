package cuvee.c

import java.io.Reader

import cuvee.Config
import cuvee.core.Cmd

// C starts from the state and the declarations of the SMT-LIB prelude, the parser builds expressions on Int and Bool directly,
// hence no overloaded operators remain to be resolved;
// the whole translation unit is parsed at once, such that the modified global variables can be inferred
object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    new Typedefs(new Scanner(reader))

  def newParser() =
    val (init, _, prelude) = cuvee.smtlib.Source.newParser()
    (init, new Unit(new Parser(init)), prelude)

  // the translation unit, which is resolved for the data model of the configuration (see input)
  class Unit(val resolver: Parser) extends easyparse.Parser[List[Cmd]]:
    def parse(in: easyparse.Input, cm: Boolean) =
      Grammar.unit.map(resolver.resolve).parse(in, cm)

  override def input(config: Config, reader: Reader, parser: easyparse.Parser[List[Cmd]]): LazyList[Cmd] =
    parser match
      case unit: Unit => unit.resolver.arch = config.arch
    super.input(config, reader, parser)
