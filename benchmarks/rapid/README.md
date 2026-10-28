# The RAPID benchmarks

33 array programs in Boogie with quantified postconditions, from the evaluation of the RAPID prover (Georgiou,
Gleiss, Kovács: trace logic for the verification of loops), as collected in the original Cuvée repository
(`benchmarks/rapid` there). Each has one procedure with one loop and no invariant; all are expected to be correct.

## Adjustments

The programs are adjusted to standard Boogie, as the Boogie frontend of Cuvée parses it:

- quantifiers in parentheses, `ensures (forall j: int :: ...)`, also nested ones (`(exists pos2: int :: ...)`);
- local variables declared at the start of the body without an initializer, `var i: int;`, with the initializer as
  an assignment in its place (`i := 0;`);
- the procedure named `main`, such that one entry point serves all tasks (`-entry main`, which `-chc` needs);
- in `increment_by_one_harder` and `swap`, the arrays whose initial values the postconditions read by `old(a)` are
  global variables that the procedure and its loop modify (`modifies a;`, also on the loop, as the Boogie frontend
  requires), instead of output parameters: in Boogie, `old` refers to the values of global variables at the entry,
  and `old(a)` of an output parameter is `a` itself, which makes the postconditions false (Cuvée answered
  incorrect), while RAPID reads it as the initial value.

The contracts and the bodies are otherwise unchanged.

## Tasks

`<name>.yml` is the task definition of `<name>.bpl` for BenchExec, with the property file
`properties/unreach-call.prp` and the expected verdict true, as for the Dafny tasks of `benchmarks/sv-comp`;
`rapid.set` lists them. The run definition `RAPID_unreach-call` of `xml/cuvee.xml`, `xml/cuvee-fallback.xml` and
`xml/cuvee-chc.xml` takes them as the tasks `Boogie.unreach-call.RAPID`.
