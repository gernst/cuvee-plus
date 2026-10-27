// ./Cuvee.sh -teq -include teq:aggregation -include teq:counters -entry phase -prove examples/dafny/teq/counters_phase_mod.dfy
// a value that adds 2 after a threshold and keeps its value before it (mono-crafted_12 of loops-crafted-1) keeps its
// remainder modulo 2, whatever the number of additions

method phase(bound: int) returns (zz: int)
  requires 0 < bound
  ensures zz % 2 == 0
{
  var pos: int;
  pos := 0;
  zz := 0;
  while pos < bound
  {
    if pos >= 5000 {
      zz := zz + 2;
    }
    pos := pos + 1;
  }
}
