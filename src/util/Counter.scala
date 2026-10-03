package util

trait Counter:
  var index = 0

  def next() =
    index = index + 1
    index

  def reset() =
    index = 0
