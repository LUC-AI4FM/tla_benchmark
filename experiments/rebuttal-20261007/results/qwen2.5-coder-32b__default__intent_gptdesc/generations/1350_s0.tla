------------------------------- MODULE CounterStateMachine -------------------------------
EXTENDS Naturals, TLC

CONSTANTS MaxValue

VARIABLES counter

Init == counter = 1

Next ==
    \/ /\ counter < MaxValue
       /\ counter' = counter + 1
    \/ /\ counter = MaxValue
       /\ counter' = counter

Spec ==
    /\ Init
    /\ [][Next]_<<counter>>
    /\ WF_next(<<counter>>)

WF_next(vars) == 
    \A s \in StateSpace: Enabled(s, Next) => \E t \in StateSpace: s -> t \in vars

StateSpace == {s \in [counter : 1..MaxValue]}

Enabled(state, action) ==
    \/ /\ state[counter] < MaxValue
       /\ action = [state EXCEPT ![counter] = state[counter] + 1]
    \/ /\ state[counter] = MaxValue
       /\ action = [state EXCEPT ![counter] = state[counter]]

Safety == 
    \A s, t \in StateSpace: s -> t \in <<counter>> => 
        \/ /\ s[counter] < MaxValue
           /\ t[counter] = s[counter] + 1
        \/ /\ s[counter] = MaxValue
           /\ t[counter] = s[counter]

Liveness ==
    <>[](counter = MaxValue)

Bounds == 
    \A s \in StateSpace: 1 <= s[counter] /\ s[counter] <= MaxValue

Monotonicity ==
    \A s, t \in StateSpace: s -> t \in <<counter>> => s[counter] <= t[counter]

THEOREM Spec => []Safety
THEOREM Spec => Liveness
THEOREM Spec => []Bounds
THEOREM Spec => []Monotonicity

=============================================================================