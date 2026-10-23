// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-invgen/id_trans.dfy
// SV-COMP loop-invgen/id_trans.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks 0 <= j; j < material_length; 0 <= j/4; j/4 < nlen

method main() returns (result: int) {
  var idBitLength: int;
  var material_length: int;
  var nlen: int;
  var j: int;
  var k: int;
  nlen := *;
  idBitLength := *;
  material_length := *;
  if nlen != (quot(idBitLength, 32)) {
    result := 0;
    return;
  }
  j := 0;
  while j < (quot(idBitLength, 8)) && j < material_length {
    assert 0 <= j;
    assert j < material_length;
    assert 0 <= (quot(j, 4));
    assert (quot(j, 4)) < nlen;
    j := j + 1;
  }
  result := 0;
  return;
}
