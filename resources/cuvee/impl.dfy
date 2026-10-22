// the entry of the implementations, which is injected before the modules of -include impl:<name> (see Config.features
// and Impl.modules): what the implementations share, the counter ticks, which numbers the evaluations of
// nondeterministic implementations and only increases, and the oracle nondet, which reads a nondeterministic value
// at a value of the counter; nondet has no axioms, hence it cannot make the task inconsistent
// (see ideas/implementations.md)

var {:impl} ticks: int

function {:impl} nondet<a>(k: int): a
