------------------------------- MODULE CounterOpArgs -------------------------------
EXTENDS Naturals

CONSTANT CONSTOP(_)

VARIABLE x

vars == << x >>

----------------------------- MODULE AbstractProps -----------------------------
EXTENDS Naturals

VARIABLE y

Inner(F(_), v) == F(v)

Prop(F(_), v) == [](F(v))

Outer(F(_), v) == [](Inner(F, v))

StateProp(v) == [](v \in 0..8)

DefOp(n) == n \in 0..8

StateInBounds == y \in 0..8
=================================================================================