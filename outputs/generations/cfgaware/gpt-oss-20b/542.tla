------------------------------ MODULE SimplePlus ------------------------------
EXTENDS Naturals

VARIABLES x, pc

vars == <<x, pc>>

Init ==
  /\ x = 0
  /\ pc = [p \in {"ProcA","ProcB"} |-> "Start"]

ProcAction(proc) ==
  /\ pc[proc] = "Start"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT ![proc] = "Done"]

ProcAAction == ProcAction("ProcA")
ProcBAction == ProcAction("ProcB")

Terminating ==
  /\ pc["ProcA"] = "Done"
  /\ pc["ProcB"] = "Done"
  /\ UNCHANGED <<x, pc>>

Next == ProcAAction \/ ProcBAction \/ Terminating

Spec == Init /\ [][Next]_vars
=============================================================================