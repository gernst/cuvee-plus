// the background theory of C, written in Boogie, which the C frontend parses after the prelude of SMT-LIB
// and injects at the beginning of the commands (see cuvee.c.Source),
// where each declaration names the languages that it is part of by their file extensions, here {:c},
// and the output in one of these languages drops it (see cuvee.pipe.Sink.filter)

// pointers to values of type a: the null pointer, and the others by their address
data {:c} Ptr<a> = null | ptr(addr: int);

// the pointee of untyped pointers, void * as Ptr<Void>, whose values carry no information
data {:c} Void = void;
