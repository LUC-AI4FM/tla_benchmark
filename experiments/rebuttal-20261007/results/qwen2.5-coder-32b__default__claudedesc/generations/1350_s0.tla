------------------------------- MODULE Github1037 -------------------------------
EXTENDS Naturals

CONSTANTS MaxValue

VARIABLES x

Init == x = 1

Next ==
    \/ /\ x < MaxValue
       /\ x' = x + 1
    \/ /\ x = MaxValue
       /\ x' = x

Spec ==
    Init /\ [][Next]_<<x>> /\ WF_next(<<x>>)

WF_next(vars) == 
    \A s \in StateSpace: Enabled(s, Next) => <>Next<_vars>

StateSpace == {s \in [VARIABLES -> DOMAIN]: TRUE}

Enabled(state, action) ==
    LET new_state == [state EXCEPT ![x] = CHOOSE x': action]
    IN  /\ state \in StateSpace
        /\ new_state \in StateSpace

Liveness ==
    (x = 1) => <>[](x = MaxValue)

=============================================================================