; cancellation laws of the boolean connectives
(declare-const p Bool)
(declare-const q Bool)
(assert false)
(assert (and p q))
(assert p)
(assert q)
(assert p)
(assert p)
