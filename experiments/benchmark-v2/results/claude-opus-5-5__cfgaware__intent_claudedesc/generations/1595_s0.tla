---------------------------- MODULE FairCounter ----------------------------
EXTENDS Naturals, TLC

VARIABLES counter, pc

vars == << counter, pc >>

Init == /\ counter = 0
        /\ pc = "Loop"

Loop == /\ pc = "Loop"
        /\ IF counter < 10
              THEN /\ counter' = counter + 1
                   /\ pc' = "Loop"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED counter

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == Loop \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Loop)

TypeOK == /\ counter \in 0..10
          /\ pc \in {"Loop", "Done"}

Termination == <>(pc = "Done" /\ counter = 10)

AtFive == counter = 5

FinishLoop == counter = 9 /\ pc = "Loop"

ASSUME TLCSet(1, 0) /\ TLCSet(2, 0)

_POSSIBLE == /\ (AtFive => TLCSet(1, TLCGet(1) + 1))
             /\ (FinishLoop => TLCSet(2, TLCGet(2) + 1))

PossibleCounts == /\ TLCGet(1) = 1
                  /\ TLCGet(2) = 1

=============================================================================