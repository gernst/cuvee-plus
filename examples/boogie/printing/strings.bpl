// ./Cuvee.sh examples/boogie/printing/strings.bpl
// string literals escape double quotes and backslashes, which print back the same way
axiom "a \"quoted\" \\ string" == "x";
