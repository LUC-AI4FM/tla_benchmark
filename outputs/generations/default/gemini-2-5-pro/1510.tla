---- MODULE SimpleStateMachine ----
EXTENDS Integers, Functions

CONSTANT S
ASSUME S = 1..5

VARIABLES x, y

vars == <<x, y>>

Foo(cur_x, cur_y) ==
    IF cur_x = 1
    THEN [cur_y EXCEPT ![cur_x] = 42]
    ELSE cur_y

Init ==
    /\ x \in S
    /\ y = [i \in S |-> 0]

Next ==
    /\ x' = x
    /\ y' = Foo(x, y)

Spec == Init /\ [][Next]_vars

====