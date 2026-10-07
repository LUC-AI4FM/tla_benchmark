------------------------------ MODULE Github702 ------------------------------
EXTENDS Naturals

VARIABLES y, z

fizzbuzz == 42

U == INSTANCE x_unchanged WITH x <- fizzbuzz, y <- y, z <- z

Init == U!Init
Next == U!Next
Spec == U!Spec
=============================================================================