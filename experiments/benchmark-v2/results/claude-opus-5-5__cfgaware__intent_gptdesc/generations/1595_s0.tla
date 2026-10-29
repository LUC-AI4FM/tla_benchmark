---- MODULE FairLoopCounter ----
EXTENDS Naturals

CONSTANT Bound
ASSUME Bound \in Nat

Max == 10

VARIABLES counter, pc

vars == << counter, pc >>

TypeOK ==
    /\ counter \in 0..Max
    /\ pc \in {"Loop", "Done"}

Init ==
    /\ counter = 0
    /\ pc = "Loop"

Increment ==
    /\ pc = "Loop"
    /\ counter < Max
    /\ counter' = counter + 1
    /\ UNCHANGED pc

Exit ==
    /\ pc = "Loop"
    /\ counter >= Max
    /\ pc' = "Done"
    /\ UNCHANGED counter

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Increment \/ Exit \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment \/ Exit)

----------------------------------------------------------------------------
\* Safety: the counter never decreases and never skips values.
Monotone == [][counter' = counter + 1 \/ counter' = counter]_vars

CounterBounded == counter <= Max

\* Progress / termination: eventually the process reaches the terminated state.
Termination == <>(pc = "Done" /\ counter = Max)

\* Liveness checkpoints.
AtFive == counter = 5

FinishLoop == counter = Max - 1 /\ counter' = Max

PossibleCounts == <>AtFive /\ <><<FinishLoop>>_vars

_POSSIBLE == PossibleCounts

====