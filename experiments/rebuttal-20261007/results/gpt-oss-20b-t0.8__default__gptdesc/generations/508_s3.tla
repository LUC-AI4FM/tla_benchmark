MODULE SmallPlusCal
EXTENDS Naturals

VARIABLES x, pc

Init == 
  /\ x \in 1..10
  /\ pc = "Start"

Next ==
  \/ /\ pc = "Start"
     /\ x*x <= 100
     /\ pc' = "Done" /\ UNCHANGED x
  \/ /\ pc = "Done"
     /\ UNCHANGED <<pc, x>>

Spec == Init /\ [][Next]_<<x, pc>> 

Termination == <> (pc = "Done")