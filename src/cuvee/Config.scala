package cuvee

import java.io.IOException

import scala.annotation.targetName

import cuvee.core._
import cuvee.pipe._

case class Config(
    source: Source,
    sink: Sink,
    printer: Printer
)

