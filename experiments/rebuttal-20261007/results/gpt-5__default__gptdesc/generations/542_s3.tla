------------------------------ MODULE TwoProcsInc ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS X0
ASSUME X0 \in Nat

VARIABLES x, pc

ProcSet == {"ProcA", "ProcB"}
Labels  == {"Inc", "Done"}

Vars == << x, pc >>

DoneSet == { p \in ProcSet : pc[p] = "Done" }
DoneAll == \A p \in ProcSet : pc[p] = "Done"

Init ==
  /\ x = X0
  /\ pc = [ p \in ProcSet |-> "Inc" ]

A_Inc ==
  /\ pc["ProcA"] = "Inc"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

B_Inc ==
  /\ pc["ProcB"] = "Inc"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

Terminating ==
  /\ DoneAll
  /\ UNCHANGED Vars

Next ==
  A_Inc \/ B_Inc \/ Terminating

Spec ==
  Init /\ [][Next]_Vars

(*
  Safety invariants
*)
TypeOK ==
  /\ x \in Nat
  /\ pc \in [ProcSet -> Labels]

CountMatches ==
  x = X0 + Cardinality(DoneSet)

(*
  Liveness property: eventually, all processes reach Done.
*)
Termination ==
  <> DoneAll

=============================================================================