---- MODULE module ----
EXTENDS Integers, Functions

VARIABLES x, y

Foo(f, v) == IF v = 1 THEN [f EXCEPT ![v] = 42] ELSE f

Init ==
    /\ x \in 1..5
    /\ y = [i \in 1..5 |-> 0]

Next ==
    /\ x' = x
    /\ y' = Foo(y, x)

Spec == Init /\ [][Next]_<<x,y>>

====================