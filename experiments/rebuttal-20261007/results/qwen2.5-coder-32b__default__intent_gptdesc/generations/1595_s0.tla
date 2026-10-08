------------------------------- MODULE CounterLoop -------------------------------
EXTENDS Naturals, TLC

CONSTANTS Bound

VARIABLES counter, terminated

Init == /\ counter = 0
        /\ terminated = FALSE

Next ==
    \/ /\ \neg terminated
       /\ counter < Bound
       /\ counter' = counter + 1
       /\ terminated' = FALSE
    \/ /\ \neg terminated
       /\ counter >= Bound
       /\ counter' = counter
       /\ terminated' = TRUE
    \/ /\ terminated
       /\ counter' = counter
       /\ terminated' = terminated

Spec ==
    /\ Init
    /\ [][Next]_<<counter, terminated>>
    /\ WF_[Next]_<<counter, terminated>>

\* Safety properties
InvCounterNonDecreasing == \A c \in Nat : c <= counter => c <= counter'
InvNoSkipValues == \A c \in Nat : counter' = c => counter = c - 1 \/ counter = counter'

\* Progress/termination property
Termination == <>(terminated)

\* Liveness checkpoints
Checkpoint5 == <>(counter = 5)
FinalTransition == <>(/\ counter = Bound - 1
                      /\ counter' = Bound)

=============================================================================