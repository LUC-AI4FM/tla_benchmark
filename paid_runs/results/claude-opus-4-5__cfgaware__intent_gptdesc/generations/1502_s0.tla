---------------------------- MODULE Specification ----------------------------

CONSTANTS Op, Forty2, InvariantSet, InitialState

VARIABLES state

-----------------------------------------------------------------------------

Init == state = InitialState

Next == 
    /\ Op[state] /= {}
    /\ state' \in Op[state]

-----------------------------------------------------------------------------

TypeInvariant == state \in DOMAIN Op

SafetyInvariant == state \in InvariantSet

Invariant == SafetyInvariant

-----------------------------------------------------------------------------

NoDeadlock == Op[state] /= {} => ENABLED(Next)

Fairness == WF_state(Next)

Spec == Init /\ [][Next]_state /\ Fairness

LiveSpec == Init /\ [][Next]_state /\ Fairness

-----------------------------------------------------------------------------

CanProgress == [](Op[state] /= {} => <><<Next>>_state)

EventuallyForty2 == <>(state = Forty2)

ReachForty2 == <>(state = Forty2)

AlwaysCanReachForty2 == []<>(state = Forty2)

-----------------------------------------------------------------------------

Reachable(P(_)) == <>(P(state))

StateInSet(S) == state \in S

EventuallyInSet(S) == <>(state \in S)

AlwaysInSet(S) == [](state \in S)

-----------------------------------------------------------------------------

DeadlockFree == [](Op[state] /= {} => ENABLED(Next))

ProgressWhenPossible == [](Op[state] /= {} => <><<Next>>_state)

=============================================================================