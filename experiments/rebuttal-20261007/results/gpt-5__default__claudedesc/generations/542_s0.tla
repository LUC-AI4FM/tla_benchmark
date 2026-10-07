---- MODULE TwoProcessIncrements ----
EXTENDS Naturals

CONSTANTS ProcSet
ASSUME ProcSet = {"ProcA", "ProcB"}

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x = 0
  /\ pc = [ p \in ProcSet |-> IF p = "ProcA" THEN "a" ELSE "b" ]

A ==
  /\ pc["ProcA"] = "a"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

B ==
  /\ pc["ProcB"] = "b"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

Terminating ==
  /\ pc["ProcA"] = "Done" /\ pc["ProcB"] = "Done"
  /\ UNCHANGED vars

Next == A \/ B \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <> (pc["ProcA"] = "Done" /\ pc["ProcB"] = "Done")
====