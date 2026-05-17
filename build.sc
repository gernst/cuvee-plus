import mill._
import mill.scalalib._
import mill.api.Task.Simple

object cuvee extends ScalaModule:
  def scalaVersion = "3.8.1"

  def mvnDeps = Seq(
    mvn"com.lihaoyi::sourcecode:0.4.4"
  )
