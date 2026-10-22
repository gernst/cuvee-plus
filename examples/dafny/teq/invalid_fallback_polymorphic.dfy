// ./Cuvee.sh -teq -fallback -quiet examples/dafny/teq/invalid_fallback_polymorphic.dfy
// a polymorphic lemma that is not free cannot be lowered, unlike a free one, which is dropped (Fallback)
lemma same<a>(ys: List<a>)
  ensures ys == ys
{
}
