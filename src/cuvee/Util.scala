package cuvee

import java.io.Reader

case class Name(name: String, index: Option[Int])

object Name:
  given Conversion[String, Name] =
    (name: String) => Name(name, None)
