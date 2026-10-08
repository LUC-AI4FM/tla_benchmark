--------------------------- MODULE SmallCheck ----------------------------
EXTENDS Naturals

VARIABLES x, pc

vars == <<x, pc>>

Init ==
  /\ x \in 1..10
  /\ pc = "Start"

DoCheck ==
  /\ pc = "Start"
  /\ x*x <= 100
  /\ pc' = "Done"
  /\ UNCHANGED x

Stutter ==
  /\ pc = "Done"
  /\ pc' = pc
  /\ UNCHANGED x

Next == DoCheck \/ Stutter

Spec == Init /\ [][Next]_vars /\ <> (pc = "Done")

SafetyInvariant == [] (x*x <= 100)

THEOREM Safety == SafetyInvariant
=============================================================================