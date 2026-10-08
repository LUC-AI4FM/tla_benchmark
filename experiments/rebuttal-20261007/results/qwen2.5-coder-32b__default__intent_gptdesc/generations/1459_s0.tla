------------------------------- MODULE NonDecreasingCounter -------------------------------
EXTENDS Naturals, TLC

CONSTANTS UpperThreshold \* The upper threshold value for the counter

VARIABLES state \* The current state of the counter

Init == state = 0

Next ==
    \/ /\ state < UpperThreshold
       /\ state' = state + 1
    \/ state' = state

Spec ==
    /\ Init
    /\ [][Next]_<<state>>
    /\ WF_next(<<state>>)

\* Safety properties
TypeOK == state \in Nat
NeverDecrease == \A s \in Seq(Nat) : \A i \in 1..Len(s)-1 : s[i] <= s[i+1]
WithinBounds == state <= UpperThreshold

SafetyProperties ==
    /\ TypeOK
    /\ NeverDecrease
    /\ WithinBounds

\* Liveness property
ReachSaturation == <>(state = UpperThreshold)

Invariant ==
    /\ SafetyProperties

THEOREM Spec => []Invariant

LIVENESS ==
    Spec => ReachSaturation

=============================================================================