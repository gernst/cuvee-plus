package easyparse

// extension [A](p: Parser[List[A]])
//   def ::[B >: A](q: Parser[B]): Parser[List[B]] =
//     (q ~ p) { case (a, as) => a :: as }

//   def ++[B >: A](q: Parser[List[B]]): Parser[List[B]] =
//     (p ~ q) { case (as, bs) => as ++ bs }

extension [B](f: => B)
  def apply(p: Scanner): Parser[B] =
    p.map { f }

extension [A1, B](f: A1 => B)
  def apply(p: Parser[A1]): Parser[B] =
    p.map { case a1 => f(a1) }

extension [A1, A2, B](f: (A1, A2) => B)
  def apply(p: Parser[A1 ~ A2]): Parser[B] =
    p.map { case a1 ~ a2 => f(a1, a2) }

extension [A1, A2, A3, B](f: (A1, A2, A3) => B)
  def apply(p: Parser[A1 ~ A2 ~ A3]): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 => f(a1, a2, a3) }

extension [A1, A2, A3, A4, B](f: (A1, A2, A3, A4) => B)
  def apply(p: Parser[A1 ~ A2 ~ A3 ~ A4]): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 => f(a1, a2, a3, a4) }

extension [A1, A2, A3, A4, A5, B](f: (A1, A2, A3, A4, A5) => B)
  def apply(p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5]): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 => f(a1, a2, a3, a4, a5) }

extension [A1, A2, A3, A4, A5, A6, B](f: (A1, A2, A3, A4, A5, A6) => B)
  def apply(p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5 ~ A6]): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 ~ a6 => f(a1, a2, a3, a4, a5, a6) }

extension [A1, A2, A3, A4, A5, A6, A7, B](f: (A1, A2, A3, A4, A5, A6, A7) => B)
  def apply(p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5 ~ A6 ~ A7]): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 ~ a6 ~ a7 =>
      f(a1, a2, a3, a4, a5, a6, a7)
    }

extension [A1, A2, A3, A4, A5, A6, A7, A8, B](f: (A1, A2, A3, A4, A5, A6, A7, A8) => B)
  def apply(p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5 ~ A6 ~ A7 ~ A8]): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 ~ a6 ~ a7 ~ a8 =>
      f(a1, a2, a3, a4, a5, a6, a7, a8)
    }

extension [A1, A2, A3, A4, A5, A6, A7, A8, A9, B](f: (A1, A2, A3, A4, A5, A6, A7, A8, A9) => B)
  def apply(p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5 ~ A6 ~ A7 ~ A8 ~ A9]): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 ~ a6 ~ a7 ~ a8 ~ a9 =>
      f(a1, a2, a3, a4, a5, a6, a7, a8, a9)
    }
