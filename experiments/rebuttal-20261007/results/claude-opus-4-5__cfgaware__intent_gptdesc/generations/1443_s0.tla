---------------------------- MODULE CyclicCounter ----------------------------

VARIABLE state

TypeInvariant == state \in {0, 1, 2}

Init == state = 0

Next == state' = (state + 1) % 3

Spec == Init /\ [][Next]_state /\ WF_state(Next)

Safety == TypeInvariant

Determinism == 
    /\ (state = 0 => ENABLED(state' = 1))
    /\ (state = 1 => ENABLED(state' = 2))
    /\ (state = 2 => ENABLED(state' = 0))

ReachState1 == <>(state = 1)

ReachState2 == <>(state = 2)

WrapAround == <>(state = 2 /\ state' = 0)

WrapAroundOccurs == <>(state = 0 /\ state # 0)

CycleLiveness == 
    /\ []<>(state = 0)
    /\ []<>(state = 1)
    /\ []<>(state = 2)

=============================================================================