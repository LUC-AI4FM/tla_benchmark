---- MODULE TwoProcInc ----
EXTENDS Naturals

VARIABLES x, pc

Proc == {"ProcA", "ProcB"}

Init ==
  /\ x = 0
  /\ pc = [p \in Proc |-> "Inc"]

ProcAInc ==
  /\ pc["ProcA"] = "Inc"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

ProcBInc ==
  /\ pc["ProcB"] = "Inc"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

Terminating ==
  /\ \A p \in Proc: pc[p] = "Done"
  /\ UNCHANGED <<x, pc>>

Next ==
  ProcAInc \/ ProcBInc \/ Terminating

vars == <<x, pc>>

AllDone == \A p \in Proc: pc[p] = "Done"

Spec ==
  Init /\ [][Next]_vars /\ <>AllDone
====