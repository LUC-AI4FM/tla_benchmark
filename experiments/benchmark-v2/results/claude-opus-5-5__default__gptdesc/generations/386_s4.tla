---------------------------- MODULE test216 ----------------------------
EXTENDS Naturals

CONSTANT D

ASSUME D + 0 = 42

THEOREM D + 0 = 42

Foo == D + 0 = 42

INSTANCE test216b WITH E <- D, y <- 0

I == INSTANCE test216b WITH E <- D, y <- 0

=============================================================================