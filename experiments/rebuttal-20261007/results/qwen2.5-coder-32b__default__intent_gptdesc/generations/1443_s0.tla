------------------------------- MODULE CyclicCounter -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS States

VARIABLES state

Init == state = 0

Next ==
    \/ /\ state = 0
       /\ state' = 1
    \/ /\ state = 1
       /\ state' = 2
    \/ /\ state = 2
       /\ state' = 0

Spec ==
    /\ Init
    /\ [][Next]_<<state>>
    /\ WF_next(<<state>>)

WF_next(vars) == 
    \A s \in States: <s> \in vars => \E s' \in States: <s'> \in vars /\ [][s = s']_vars => <>[s' = s]_vars

Safety ==
    \/ state \in {0, 1, 2}

Determinism ==
    \/ /\ state = 0 => state' = 1
       \/ state = 1 => state' = 2
       \/ state = 2 => state' = 0

Reachability ==
    <>[][state = 1]_<<state>>
    /\ <>[][state = 2]_<<state>>

WrapAround ==
    <>[state = 2]_<<state>> /\ <>[state = 0]_<<state>>

CycleLiveness ==
    \A s \in {0, 1, 2}: <>[][state = s]_<<state>>

THEOREM Spec => []Safety
THEOREM Spec => []Determinism
THEOREM Spec => Reachability
THEOREM Spec => WrapAround
THEOREM Spec => CycleLiveness

=============================================================================