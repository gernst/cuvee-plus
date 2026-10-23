It can never happen that the resulting type of an operation
is a signed-integer type but the resulting value is not in the
range of values that are representable by that type.
A violation of this property matches what C11 defines as undefined behavior due to an unrepresentable result,
i.e., only the following operations are considered:
* addition (binary `+`),
* subtraction (binary `-`),
* multiplication (binary `*`),
* negation (unary `-`),
* division (binary `/`),
* bitwise left shift (binary `<<`).

As such, the following do not violate this property:
* casts/conversions to signed-integer types,
* `abs(INT_MIN)`, `labs(LONG_MIN)`, `llabs(LLONG_MIN)`, `imaxabs(INTMAX_MIN)`.
