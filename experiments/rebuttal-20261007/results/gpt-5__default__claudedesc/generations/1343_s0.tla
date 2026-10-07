---- MODULE MinimalStutter ----
EXTENDS Naturals

CONSTANTS Dummy

VARIABLES x, y

Init ==
  /\ x = 0
  /\ y = 0
  /\ y = x

Next == UNCHANGED <<x, y>>

Spec == Init /\ [][UNCHANGED <<x, y>>]_<<x, y>>

====