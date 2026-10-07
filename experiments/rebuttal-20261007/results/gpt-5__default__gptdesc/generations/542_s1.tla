---------------------------- MODULE IncrementOnce ----------------------------

EXTENDS Naturals

CONSTANTS Dummy

VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"ProcA", "ProcB"}

Init ==
  /\ x = 0
  /\ pc = ["ProcA" |-> "A1", "ProcB" |-> "B1"]

AllDone == \A p \in ProcSet: pc[p] = "Done"

A1 ==
  /\ pc["ProcA"] = "A1"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

B1 ==
  /\ pc["ProcB"] = "B1"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

Terminating ==
  /\ AllDone
  /\ UNCHANGED vars

Next == A1 \/ B1 \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(A1)
  /\ WF_vars(B1)

\* Safety invariants
TypeOK == /\ x \in Nat
          /\ pc \in [ProcSet -> {"A1", "B1", "Done"}]

BoundedX == x \in 0..2

DoneImpliesValue == AllDone => x = 2

\* Liveness property: eventual termination
Termination == <>AllDone

=============================================================================