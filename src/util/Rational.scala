package util

implicit def toRational(n: Int): Rational =
  Rational(n)

case class Rational private (num: BigInt, den: BigInt):
  require(den > 0)

  def isZero =
    num == 0

  def isPositive =
    num > 0

  def isNegative =
    num < 0

  def unary_- : Rational =
    Rational(-this.num, this.den)

  def +(that: Rational): Rational =
    Rational(this.num * that.den + that.num * this.den, this.den * that.den)

  def -(that: Rational): Rational =
    Rational(this.num * that.den - that.num * this.den, this.den * that.den)

  def *(that: Rational): Rational =
    Rational(this.num * that.num, this.den * that.den)

  def /(that: Rational): Rational =
    Rational(this.num * that.den, this.den * that.num)

  def <(that: Rational): Boolean =
    this.num * that.den < that.num * this.den

  def <=(that: Rational): Boolean =
    this < that || this == that

  // the decimal digits of a nonnegative rational with at least one digit after the point, e.g. 2.0 or 0.125,
  // if the denominator has no prime factors other than 2 and 5
  def decimal: Option[String] =
    require(!isNegative)

    def powers(n: BigInt, p: Int, k: Int): (BigInt, Int) =
      if n % p == 0 then powers(n / p, p, k + 1) else (n, k)

    val (rest2, k2) = powers(den, 2, 0)
    val (rest5, k5) = powers(rest2, 5, 0)

    if rest5 != 1
    then None
    else
      val k = k2 max k5 max 1
      val digits = (num * BigInt(10).pow(k) / den).toString.reverse.padTo(k + 1, '0').reverse
      Some(digits.dropRight(k) + "." + digits.takeRight(k))

object Rational:
  def apply(num: BigInt) =
    new Rational(num, 1)

  def apply(num: BigInt, den: BigInt): Rational =
    val n = num.gcd(den)
    if den < 0
    then new Rational(-num / n, -den / n)
    else new Rational(num / n, den / n)

  // decimal literals, e.g. 12.345 or 2
  def decimal(digits: String): Rational =
    digits.split('.') match
      case Array(whole)           => Rational(BigInt(whole))
      case Array(whole, fraction) => Rational(BigInt(whole + fraction), BigInt(10).pow(fraction.length))
      case _                      => throw new NumberFormatException("invalid decimal: " + digits)
