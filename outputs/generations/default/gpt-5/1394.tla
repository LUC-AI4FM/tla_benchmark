--------------------------- MODULE Github702 ---------------------------
(*
  Primary module that models a TLC issue where an identifier can become
  undefined inside an UNCHANGED expression during next-state computation.

  It declares state variables y and z, defines a constant-valued operator
  fizzbuzz, and instantiates the x_unchanged module with the substitution
  x <- fizzbuzz.
*)
EXTENDS Naturals

CONSTANTS Dummy

VARIABLES y, z

fizzbuzz == 3

U == INSTANCE x_unchanged
       WITH x <- fizzbuzz,
            y <- y,
            z <- z

Init == U!Init

Next == U!Next

Spec == U!Spec
=============================================================================