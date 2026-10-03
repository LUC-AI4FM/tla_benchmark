---------------------------- MODULE FairCounter ----------------------------

EXTENDS Naturals

CONSTANTS Max
ASSUME Max = 10

VARIABLES pc, x

vars == << pc, x >>

Init ==
  /\ pc = "Loop"
  /\ x = 0

Incr ==
  /\ pc = "Loop"
  /\ x < Max
  /\ x' = x + 1
  /\ pc' = "Loop"

ToDone ==
  /\ pc = "Loop"
  /\ x >= Max
  /\ pc' = "Done"
  /\ UNCHANGED x

Next == Incr \/ ToDone

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariants
TypeOK == /\ pc \in {"Loop", "Done"}
          /\ x \in Nat

WithinBounds == x <= Max

DoneImpliesMax == (pc = "Done") => x = Max

Inv == TypeOK /\ WithinBounds /\ DoneImpliesMax
Safety == []Inv

\* Liveness property: termination
Termination == <> (pc = "Done")

\* Auxiliary predicates
AtFive == x = 5

FinishLoop == /\ pc = "Done"
              /\ x = Max

\* TLC-based check about named-state counts (for exploration)
\* Exactly one visit to AtFive (when Max >= 5) and one to FinishLoop along the main path.
PossibleCounts ==
  [ "AtFive" |-> IF Max >= 5 THEN 1 ELSE 0,
    "FinishLoop" |-> 1 ]

============================================================================