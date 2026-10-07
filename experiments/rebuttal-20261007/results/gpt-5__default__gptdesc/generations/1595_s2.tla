----------------------------- MODULE FairSequentialCounter -----------------------------

EXTENDS Naturals

CONSTANT N
ASSUME N \in Nat /\ N = 10

VARIABLES x, pc

vars == << x, pc >>

Init ==
  /\ x = 0
  /\ pc = "Loop"

StepInc ==
  /\ pc = "Loop"
  /\ x < N
  /\ x' = x + 1
  /\ pc' = "Loop"

StepExit ==
  /\ pc = "Loop"
  /\ x >= N
  /\ UNCHANGED x
  /\ pc' = "Done"

Next == StepInc \/ StepExit

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

\* Safety invariants
SafetyInv ==
  /\ x \in 0..N
  /\ pc \in {"Loop", "Done"}

\* Liveness (termination) property
Termination == <> (pc = "Done")

\* Auxiliary predicates
AtFive == x = 5

FinishLoop ==
  /\ pc = "Done"
  /\ x = N

\* TLC-based check for the set of possible counter values
PossibleCounts == 0..N

========================================================================================