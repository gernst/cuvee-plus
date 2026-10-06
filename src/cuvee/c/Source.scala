package cuvee.c

import java.io.Reader

import scala.collection.mutable

import cuvee.core.Cmd

// C starts from the state and the declarations of the SMT-LIB prelude, the parser builds expressions on Int and Bool directly,
// hence no overloaded operators remain to be resolved;
// like the other frontends, each call parses a single top-level declaration, such that errors point at it,
// but the declarations are buffered and the whole translation unit is resolved at the end of the input,
// such that the modified global variables can be inferred
object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    new Scanner(reader)

  def newParser() =
    val (init, _, prelude) = cuvee.smtlib.Source.newParser()
    val parser = new Parser(init)
    val tops = mutable.ListBuffer[Top]()

    val unit = new easyparse.Parser[List[Cmd]]:
      def parse(in: easyparse.Input, cm: Boolean) =
        val (top, in_) = Grammar.top.parse(in, cm)
        tops += top
        if done(in_)
        then (parser.resolve(tops.toList), in_)
        else (Nil, in_)

    (init, unit, prelude)
