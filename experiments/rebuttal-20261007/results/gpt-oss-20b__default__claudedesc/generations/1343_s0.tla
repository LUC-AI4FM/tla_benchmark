------------------------------ MODULE Test ------------------------------
EXTENDS Naturals

VARIABLES x, y

Init == 
  /\ x = 0
  /\ y = 0
  /\ y = x

Stutter == UNCHANGED <<x, y>>

Spec == Init /\ [] Stutter

=============================================================================