package cuvee.core

object Zero extends Lit(BigInt(0), Sort.int)
object One extends Lit(BigInt(1), Sort.int)

object True extends App(Fun.true_, Nil, Sort.bool, Nil)
object False extends App(Fun.false_, Nil, Sort.bool, Nil)
