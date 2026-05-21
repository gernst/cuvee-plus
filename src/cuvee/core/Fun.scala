package cuvee.core

import cuvee.Name
import scala.annotation.targetName

case class Fun(name: Name, params: List[Param], args: List[Type], res: Type)
