------------------------------- MODULE PlusCalExample -------------------------------
EXTENDS Integers, TLC, Sequences

CONSTANTS ProcSet

VARIABLES x, pc

Init == 
  /\ x = 0 
  /\ pc = [p \in ProcSet |-> "Start"]

Next ==
  \/ /\ pc["ProcA"] = "Start"
     /\ pc' = [pc EXCEPT ![ProcA] = "Done"]
     /\ x' = x + 1
     /\ pc'["ProcB"] = pc["ProcB"]
  \/ /\ pc["ProcB"] = "Start"
     /\ pc' = [pc EXCEPT ![ProcB] = "Done"]
     /\ x' = x + 1
     /\ pc'["ProcA"] = pc["ProcA"]
  \/ Terminating

Terminating ==
  /\ \A p \in ProcSet: pc[p] = "Done"
  /\ UNCHANGED <<x, pc>>

Spec ==
  Init /\ [][Next]_<<x, pc>> /\ <><Terminating>_<<x, pc>>

THEOREM Spec => []<>(\A p \in ProcSet: pc[p] = "Done")

=============================================================================