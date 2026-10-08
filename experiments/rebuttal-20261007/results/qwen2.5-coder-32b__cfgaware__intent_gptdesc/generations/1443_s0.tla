------------------------------- MODULE CyclicCounter -------------------------------

CONSTANTS State

VARIABLES current

Init == current = 0

Next ==
    \/ /\ current = 0
       /\ current' = 1
    \/ /\ current = 1
       /\ current' = 2
    \/ /\ current = 2
       /\ current' = 0

Spec ==
    Init /\ [][Next]_<<current>>

Safety == \A s \in State: s \notin {0, 1, 2} => ~<>(current = s)

DeterministicNext ==
    \A s \in {0, 1, 2}: \/ current = s => EXACTLY_ONE s' (current' = s')

ReachState1 == <>(current = 1)
ReachState2 == <>(current = 2)
WrapAround == <>(/\ current = 2
                 /\ current' = 0)

CycleLiveness ==
    \A s \in {0, 1, 2}: [](<>(current = s))

=============================================================================