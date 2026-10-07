---- MODULE TwoProcIncrement ----
EXTENDS Naturals

CONSTANTS Procs
ASSUME Procs = {"ProcA", "ProcB"}

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x = 0
  /\ pc = [p \in Procs |-> IF p = "ProcA" THEN "A1" ELSE "B1"]

AllDone ==
  \A p \in Procs: pc[p] = "Done"

AStep ==
  /\ pc["ProcA"] = "A1"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

BStep ==
  /\ pc["ProcB"] = "B1"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

Terminating ==
  /\ AllDone
  /\ UNCHANGED vars

Next ==
  AStep \/ BStep \/ Terminating

Spec ==
  Init /\ [][Next]_vars

TypeOK ==
  /\ x \in Nat
  /\ pc \in [Procs -> {"A1", "B1", "Done"}]
  /\ pc["ProcA"] \in {"A1", "Done"}
  /\ pc["ProcB"] \in {"B1", "Done"}

XBound ==
  x \in 0..2

Termination ==
  <>AllDone
==============================