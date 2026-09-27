package easyparse


// extension [A](p: Parser[List[A]])
//   def ::[B >: A](q: Parser[B]): Parser[List[B]] =
//     (q ~ p) { case (a, as) => a :: as }

//   def ++[B >: A](q: Parser[List[B]]): Parser[List[B]] =
//     (p ~ q) { case (as, bs) => as ++ bs }

extension (s: Scanner)
  infix def $[B](f: => B): Parser[B] =
    s ~ R(f)

extension [A1](p: Parser[A1])
  infix def $[B](f: A1 => B): Parser[B] =
    p.map { case (a) => f(a) }

extension [A1, A2](p: Parser[A1 ~ A2])
  infix def $[B](f: (A1, A2) => B): Parser[B] =
    p.map { case a1 ~ a2 => f(a1, a2) }

  def apply[B](f: (A1, A2) => B): Parser[B] =
    p.map { case a1 ~ a2 => f(a1, a2) }

extension [A1, A2, A3](p: Parser[A1 ~ A2 ~ A3])
  infix def $[B](f: (A1, A2, A3) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 => f(a1, a2, a3) }

extension [A1, A2, A3, A4](p: Parser[A1 ~ A2 ~ A3 ~ A4])
  infix def $[B](f: (A1, A2, A3, A4) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 => f(a1, a2, a3, a4) }

extension [A1, A2, A3, A4, A5](p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5])
  infix def $[B](f: (A1, A2, A3, A4, A5) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 => f(a1, a2, a3, a4, a5) }

extension [A1, A2, A3, A4, A5, A6](p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5 ~ A6])
  infix def $[B](f: (A1, A2, A3, A4, A5, A6) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 ~ a6 => f(a1, a2, a3, a4, a5, a6) }

extension [A1, A2, A3, A4, A5, A6, A7](p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5 ~ A6 ~ A7])
  infix def $[B](f: (A1, A2, A3, A4, A5, A6, A7) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 ~ a6 ~ a7 => f(a1, a2, a3, a4, a5, a6, a7) }

extension [A1, A2, A3, A4, A5, A6, A7, A8](p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5 ~ A6 ~ A7 ~ A8])
  infix def $[B](f: (A1, A2, A3, A4, A5, A6, A7, A8) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 ~ a6 ~ a7 ~ a8 => f(a1, a2, a3, a4, a5, a6, a7, a8) }
