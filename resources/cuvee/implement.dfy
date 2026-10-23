// the entry of the implementations, which is injected before the modules of -include implement:<name> (see Config.features
// and Implement.modules): what the implementations share, the counter ticks, which numbers the evaluations of
// nondeterministic implementations and only increases, and the oracle nondet, which reads a nondeterministic value
// at a value of the counter; nondet has no axioms, hence it cannot make the task inconsistent
// (see ideas/implementations.md)

var {:implement} ticks: int

function {:implement} nondet<a>(k: int): a
