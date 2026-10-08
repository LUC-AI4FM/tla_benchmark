---------------------------- MODULE Counter ----------------------------

CONSTANTS Limit

VARIABLES state

(*--algorithm Counter
variables state = 0;
begin
    while TRUE do
        if state < Limit then
            either
                /\ state' = state + 1
                \/ state' = state
            else
                state' = state
end algorithm*)

Init == state = 0

IncAction == (state < Limit) => <<state' = state + 1>>_<<state' \in {state, state + 1}>>

Next == IncAction /\ state' \in Nat

Spec ==
    Init /\ [][Next]_<<state>>

Inv ==
    /\ state \in Nat
    /\ state <= Limit

TypeOK ==
    /\ state \in Nat

Bounded ==
    state <= Limit

NonDecreasing ==
    \/ state' = state
    \/ state' = state + 1

NoIllegalJumps ==
    \/ state' = state
    \/ state' = state + 1

Liveness ==
    <>(state = Limit)

THEOREM Spec => []Inv
THEOREM Spec => []TypeOK
THEOREM Spec => []Bounded
THEOREM Spec => []NonDecreasing
THEOREM Spec => []NoIllegalJumps
THEOREM Spec => <>Liveness

=============================================================================