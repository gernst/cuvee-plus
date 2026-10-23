// ./Cuvee.sh -quiet examples/dafny/parsing/invalid_annotation_value.dfy
// only {:implement} of a function has a value
function {:rw x} f(x: int): int { x }
