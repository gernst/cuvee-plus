type pair<a,b>
type option<a>

type object = int
datatype context = context(x: int, y: int)

datatype heap
    = heap(rcount: int, size: int, laddr: int, lobj: object, ctx: context)
{
    method alloc(obj: object)
        returns (addr: int, that: heap)
        ensures that.rcount == this.rcount
        ensures that.size   == this.size + 1
        ensures that.laddr  == this.laddr
        ensures that.lobj   == if addr == this.laddr then obj else this.lobj
        ensures that.ctx    == this.ctx

        ensures addr == that.size
}

method test(x: int, y: int)
{
    var laddr: int, lobj: int;
    var h1: heap := heap(0, 0, laddr, lobj, context(x, y));
}