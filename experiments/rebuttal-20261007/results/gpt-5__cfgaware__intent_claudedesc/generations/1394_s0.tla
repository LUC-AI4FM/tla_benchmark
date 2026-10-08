------------------------------ MODULE Main ------------------------------

EXTENDS Integers

VARIABLES x, y

Op == 42

I == INSTANCE Sub WITH
  a <- x,
  b <- Op,
  c <- y

Spec == I!Spec

=============================================================================