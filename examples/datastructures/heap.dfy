datatype Heap<a,b>
    = Heap(h: map<a,b>)
{
    method isEmpty()
        returns (result: bool)
        ensures result == (this.h == map[])
    {
        result := this.h == map[];
    }

    method Store(key: a, value: b)
        returns (that: Heap<a,b>)
        ensures that.h == this.h[key := value]
    {
        that := Heap(this.h[key := value]);
    }

    method Load(key: a)
        returns (value: b)
        requires key in this.h
        ensures value == this.h[key]
    {
        value := this.h[key];
    }
}
