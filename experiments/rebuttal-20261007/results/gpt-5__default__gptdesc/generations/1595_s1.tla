----------------------------- MODULE FairSequentialCounter -----------------------------
EXTENDS Naturals

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x = 0
  /\ pc = "Loop"

Inc ==
  /\ pc = "Loop"
  /\ x < 10
  /\ x' = x + 1
  /\ pc' = "Loop"

DoneStep ==
  /\ pc = "Loop"
  /\ x >= 10
  /\ pc' = "Done"
  /\ UNCHANGED x

Next == Inc \/ DoneStep

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety predicates (state invariants)
TypeOK == /\ x \in Nat /\ pc \in {"Loop", "Done"}
Bounded == x <= 10

\* Auxiliary predicates
AtFive == x = 5
FinishLoop == /\ x = 10 /\ pc = "Done"

\* TLC-friendly check for counter values reachable while executing
PossibleCounts == 0..10

\* Liveness: termination property — eventually the terminal state is reached
Termination == <> (pc = "Done")
=============================================================================