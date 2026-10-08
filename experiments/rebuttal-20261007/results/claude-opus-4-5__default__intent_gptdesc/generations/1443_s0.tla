---------------------------- MODULE CyclicCounter ----------------------------

EXTENDS Naturals

VARIABLES state

\* The set of valid states
States == {0, 1, 2}

\* Initial condition: start in state 0
Init == state = 0

\* Transition relation: increment by one modulo 3
Next == state' = (state + 1) % 3

\* Specification with weak fairness to ensure progress
Spec == Init /\ [][Next]_state /\ WF_state(Next)

\* ============================================================================