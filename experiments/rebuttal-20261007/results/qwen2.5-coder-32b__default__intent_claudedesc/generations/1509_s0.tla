------------------------------- MODULE RecursiveFunctionSpec -------------------------------
EXTENDS Naturals

CONSTANTS Domain

VARIABLES state

DefineSequence(n) == IF n = 0 THEN 1 ELSE DefineSequence(n - 1) + 2

Init == /\ state \in Domain
        /\ state = DefineSequence(0)

Next == TRUE

Spec == Init /\ [][Next]_<<state>>

Invariants ==
    /\ state \in {DefineSequence(i) : i \in DOMAIN Domain}

Fairness == WF_next(state)

=============================================================================