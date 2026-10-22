// ./Cuvee.sh -include teq:aggregation -quiet examples/dafny/parsing/invalid_include_teq.dfy
// the modules of the lemma database are written over teq.dfy, hence they need -teq or -known teq (Config.injected)
method main(a: int) returns (b: int)
  ensures b == a
{
  b := a;
}
