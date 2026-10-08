----------------------------- MODULE Increment -----------------------------
EXTENDS Naturals, TLC, SETS

CONSTANTS ProcA, ProcB

VARIABLES x, pc

P == {ProcA, ProcB}

Init ==
  /\ x = 0
  /\ pc \in [P -> {"Start", "Done"}]
  /\ \A p \in P : pc[p] = "Start"

ProcAction(p) ==
  /\ pc[p] = "Start"
  /\ pc' = [pc EXCEPT ![p] = "Done"]
  /\ x' = x + 1

Terminating ==
  /\ \A p \in P : pc[p] = "Done"
  /\ UNCHANGED <<x, pc>>

Next ==
  \/ ProcAction(ProcA)
  \/ ProcAction(ProcB)
  \/ Terminating

XCountInvariant ==
  x = Card({p \in P : pc[p] = "Done"})

Spec ==
  Init
  /\ [][Next]_<<x, pc>>
  /\ []XCountInvariant
  /\ <> (\A p \in P : pc[p] = "Done")
===============================================================================