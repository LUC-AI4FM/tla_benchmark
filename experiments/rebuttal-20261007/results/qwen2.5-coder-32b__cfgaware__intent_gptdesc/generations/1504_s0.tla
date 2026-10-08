------------------------------- MODULE SimpleReactiveSystem -------------------------------

VARIABLES boolState

Init == boolState = TRUE

Next == /\ UNCHANGED boolState

Prop == /\ \A s \in StateSpace : boolState \in s -> boolState[s] = TRUE
       /\ [](<> (boolState' = boolState))

StateSpace == {s \in [][BOOL -> BOOL] : s[0] = TRUE}

=============================================================================