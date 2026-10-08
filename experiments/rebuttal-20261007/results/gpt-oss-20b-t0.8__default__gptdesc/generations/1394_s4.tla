---- MODULE x_unchanged ----
EXTENDS Naturals

CONSTANTS x

VARIABLES y, z

Init ==
  /\ y \in {1,2,3}
  /\ z \in {1,2,3}

Next ==
  /\ y' = y + 1
  /\ UNCHANGED <<x, z>>

Spec == Init /\ [][Next]_<<y,z>>
---- MODULE Github702 ----
CONSTANTS fizzbuzz

fizzbuzz == 42

INSTANCE x_unchanged WITH
   x = fizzbuzz