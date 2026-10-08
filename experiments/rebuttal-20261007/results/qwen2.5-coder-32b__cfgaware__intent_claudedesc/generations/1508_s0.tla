------------------------------- MODULE StutteringStateMachine -------------------------------

CONSTANTS
    \* No additional constants are needed for this specification

VARIABLES
    x

ASSUME Init == x = 0

Next ==
    \/ x' = 5
    \/ x' \in {1, 2, 3}
    \/ x' = 10
    \/ (x = 0 /\ x' = 1)
    \/ (x = 1 /\ x' = 0)

Spec ==
    Init /\ [][Next]_<<x>>

Invar ==
    x \in {0}

TypeOK ==
    x \in Nat

\* The stuttering-closed next-state relation
ClosedNext == Next \/ x' = x

\* The complete specification with the invariant
CompleteSpec ==
    Spec /\ []Invar

=============================================================================