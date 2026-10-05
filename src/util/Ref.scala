package util

object Ref:
  implicit def get[A](ref: Ref[A]): A =
    ref.value

class Ref[A](var value: A):
  def :=(value: A) =
    this.value = value

  def map(f: A => A) =
    value = f(value)

  // a new reference with the current value, which is updated independently
  def copy: Ref[A] =
    Ref(value)
