package util

// string literals in Dafny and Boogie, where a backslash escapes a double quote or a backslash
object Strings:
  def escape(value: String): String =
    value.replace("\\", "\\\\").replace("\"", "\\\"")

  def unescape(text: String): String =
    text.replaceAll("\\\\(.)", "$1")
