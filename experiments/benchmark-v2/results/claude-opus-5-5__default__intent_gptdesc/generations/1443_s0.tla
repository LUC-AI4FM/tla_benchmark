---------------------------- MODULE CyclicCounter ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLE state

vars == <<state>>

States == {0, 1, 2}

\* Abstract transition relation between two states
Succ(s, t) == t = (s + 1) % 3

-----------------------------------------------------------------------------
\* Initial condition
Init == state = 0

\* Allowed transition: increment modulo 3
Step == state' = (state + 1) % 3

Next == Step

\* Weak fairness ensures the cycle keeps advancing forever
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Safety: the state is always one of {0,1,2}
TypeOK == state \in States

\* Determinism of next-state, static form: each state has exactly one successor
DeterministicRelation ==
    \A s \in States : Cardinality({t \in States : Succ(s, t)}) = 1

\* The unique successors are exactly 0->1, 1->2, 2->0
SuccessorTable ==
    /\ \A t \in States : Succ(0, t) <=> (t = 1)
    /\ \A t \in States : Succ(1, t) <=> (t = 2)
    /\ \A t \in States : Succ(2, t) <=> (t = 0)

ASSUME DeterministicRelation /\ SuccessorTable

\* Determinism of next-state, behavioral form: every change of state goes
\* to the unique permitted successor
Deterministic ==
    [][ /\ (state = 0 => state' = 1)
        /\ (state = 1 => state' = 2)
        /\ (state = 2 => state' = 0) ]_vars

\* Reachability assertions
Reach1 == <>(state = 1)
Reach2 == <>(state = 2)

\* Wrap-around occurrence: the transition 2 -> 0 happens at least once
WrapAround == <><<state = 2 /\ state' = 0>>_vars

\* Cycle liveness: all three states are visited infinitely often
CycleLiveness ==
    /\ []<>(state = 0)
    /\ []<>(state = 1)
    /\ []<>(state = 2)

\* Wrap-around occurs infinitely often
InfiniteWrapAround == []<><<state = 2 /\ state' = 0>>_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => Deterministic
THEOREM Spec => Reach1 /\ Reach2
THEOREM Spec => WrapAround
THEOREM Spec => CycleLiveness /\ InfiniteWrapAround

=============================================================================