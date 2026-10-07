-------------------------- MODULE Github702 --------------------------
EXTENDS Naturals

(*
  Primary module modeling TLC issue Github#702:
  - Declares variables y and z.
  - Defines a constant-valued operator fizzbuzz.
  - Instantiates x_unchanged with substitution x <- fizzbuzz to
    exercise UNCHANGED on a non-variable expression during next-state
    computation.
*)

VARIABLES y, z

fizzbuzz == 1

XU == INSTANCE x_unchanged
  WITH x <- fizzbuzz,
       y <- y,
       z <- z

Init == XU!Init
Next == XU!Next
Spec == XU!Spec
=============================================================================