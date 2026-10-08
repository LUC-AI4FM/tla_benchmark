------------------------------- MODULE EvenOdd -------------------------------
EXTENDS Naturals, TLC

CONSTANTS N \* The natural number to check

VARIABLES state, countEvenToOdd, countOdd

Init == 
    /\ state = "START"
    /\ countEvenToOdd = 0
    /\ countOdd = 0

Next ==
    \/ /\ state = "START"
       /\ (state' = "EVEN" /\ countEvenToOdd' = 0 /\ countOdd' = 0)
    \/ /\ state = "EVEN"
       /\ \/ /\ N = 0
              /\ (state' = "DONE" /\ countEvenToOdd' = countEvenToOdd /\ countOdd' = countOdd)
          \/ /\ N > 0
              /\ (state' = "ODD" /\ countEvenToOdd' = countEvenToOdd + 1 /\ countOdd' = countOdd)
    \/ /\ state = "ODD"
       /\ \/ /\ N = 0
              /\ (state' = "DONE" /\ countEvenToOdd' = countEvenToOdd /\ countOdd' = countOdd)
          \/ /\ N > 0
              /\ (state' = "EVEN" /\ countEvenToOdd' = countEvenToOdd /\ countOdd' = countOdd + 1)

Spec ==
    Init /\ [][Next]_<<state, countEvenToOdd, countOdd>>

\* Safety invariants
TypeOK ==
    \/ state \in {"START", "EVEN", "ODD", "DONE"}
    /\ countEvenToOdd \in Nat
    /\ countOdd \in Nat

CountInvariant ==
    \/ state = "DONE"
       /\ countEvenToOdd = 3
       /\ countOdd = 3

\* Liveness properties
Termination ==
    <>[](state = "DONE")

\* Fairness conditions
WF == WFNext(Next)

THEOREM Spec => []TypeOK
THEOREM Spec => [](CountInvariant)
THEOREM Spec => Termination
THEOREM Spec => WF
=============================================================================