---- MODULE SmallStateMachine ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

Foo(f) == IF x = 1 THEN [f EXCEPT ![x] = 42] ELSE f

TypeOK ==
    /\ x \in 1..5
    /\ y \in [1..5 -> {0, 42}]

Init ==
    /\ x \in 1..5
    /\ y = [i \in {1, 2, 3, 4, 5} |-> 0]

Next ==
    /\ y' = Foo(y)
    /\ x' = x

Spec == Init /\ [][Next]_vars

====