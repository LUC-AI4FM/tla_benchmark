------------------------------- MODULE PlusCalExample -----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS ProcA, ProcB

VARIABLES x, pc

Init == 
  /\ x = 0 
  /\ pc[ProcA] = "start" 
  /\ pc[ProcB] = "start"

Next ==
  \/ /\ pc[ProcA] = "start"
     /\ pc' = [pc EXCEPT ![ProcA] = "Done"]
     /\ x' = x + 1
     /\ UNCHANGED pc[ProcB]
  \/ /\ pc[ProcB] = "start"
     /\ pc' = [pc EXCEPT ![ProcB] = "Done"]
     /\ x' = x + 1
     /\ UNCHANGED pc[ProcA]
  \/ /\ pc[ProcA] = "Done" 
     /\ pc[ProcB] = "Done" 
     /\ pc' = pc 
     /\ x' = x

Spec ==
  INIT Init
  /\ NEXT Next
  /\ []<>[](pc[ProcA] = "Done" /\ pc[ProcB] = "Done")

Fairness ==
  WF_next(S_<< <<ProcA>>, <<ProcB>> >>)

THEOREM Spec => Fairness

=============================================================================