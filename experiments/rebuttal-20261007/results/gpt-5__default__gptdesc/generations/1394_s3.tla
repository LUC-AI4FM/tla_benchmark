----------------------------- MODULE Github702 -----------------------------
EXTENDS Naturals

VARIABLES y, z

fizzbuzz == 1

X == INSTANCE x_unchanged WITH x <- fizzbuzz, y <- y, z <- z

Init == X!Init
Next == X!Next
Spec == X!Spec
============================================================================