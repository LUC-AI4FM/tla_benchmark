------------------------------- MODULE CounterSpec -------------------------------

CONSTANTS outerX

VARIABLES x

InnerStep == \/ /\ x < 3
               /\ x' = x + 1

Next == \/ InnerStep
        \/ /\ ~(x < 3)
           /\ x' = x

Spec == VARIABLES outerX
        /\ outerX = x
        /\ PC = [<<"Init">>]
        /\ Init \* Initialization predicate
        /\ [][Next]_<<x>>
        /\ WF_x(InnerStep)

Init == outerX = 0

Prop == <>(outerX = 3)

=============================================================================