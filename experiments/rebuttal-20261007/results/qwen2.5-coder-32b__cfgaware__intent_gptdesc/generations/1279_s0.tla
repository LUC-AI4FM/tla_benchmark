------------------------------- MODULE SimpleSystem -------------------------------

CONSTANTS
    InitValue \* The initial value of the state variable
    AllowedValues \* A finite set of values from which the state variable can be updated

VARIABLES
    x \* The state variable

ASSUME
    InitValue \in Int /\ InitValue > 0
    AllowedValues \subseteq Int /\ AllowedValues = {v \in Int : v > 0}

Init == x = InitValue

Next ==
    \/ \E v \in AllowedValues : x' = v
    \/ x' = x

Spec ==
    Init /\ [][Next]_<<x>>

Invariant ==
    \A s \in States: s.x # 0

TransitionConstraint ==
    \A <<s, s'>> \in Transitions:
        \/ s' = s
        \/ \E v \in AllowedValues : s'.x = v

THEOREM Spec => []Invariant

THEOREM Spec => <>[]TransitionConstraint

=============================================================================