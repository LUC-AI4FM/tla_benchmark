------------------------------- MODULE SimpleStateTransitionSystem -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    InitValue,
    InvariantSet,
    Op

VARIABLES state

Init == state = InitValue

Next ==
    /\ state \in DOMAIN Op
    /\ state' \in (Op)[state]

Spec ==
    /\ Init
    /\ [][Next]_<<state>>
    /\ [](state \in InvariantSet)

Liveness ==
    \/ \A s \in {s \in DOMAIN Op : Op[s] # {} } : <>(state = s)
    \/ \E s \in {s \in DOMAIN Op : Op[s] = {} } : [](state = s)

Fairness ==
    WF_next(<<state>>)

THEOREM Spec => []<>(/\ state \in DOMAIN Op
                      /\ (Op)[state] # {}
                      -> <>(\E s' \in (Op)[state] : state' = s'))

=================================================================================================