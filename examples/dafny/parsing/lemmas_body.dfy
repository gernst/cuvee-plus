// ./Cuvee.sh -quiet examples/dafny/parsing/lemmas_body.dfy
// the proofs of lemmas are not supported yet, their body must be absent or empty
lemma zero()
  ensures 0 == 0
{
  assert true;
}
