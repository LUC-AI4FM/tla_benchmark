----------------------------- MODULE Github702 -----------------------------
EXTENDS Naturals

VARIABLES y, z

fizzbuzz == 1

UX == INSTANCE x_unchanged WITH x <- fizzbuzz, y <- y, z <- z

Init == UX!Init
Next == UX!Next
Spec == UX!Spec
=============================================================================