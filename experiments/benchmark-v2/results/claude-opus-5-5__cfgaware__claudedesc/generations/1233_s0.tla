---- MODULE test61 ----
EXTENDS Naturals

VARIABLE y

IM(x) == INSTANCE test61a

ISpec == IM(y)!Spec

JM == INSTANCE test61a WITH x <- y

JSpec == JM!Spec

Invariant == y \in 0..4
====