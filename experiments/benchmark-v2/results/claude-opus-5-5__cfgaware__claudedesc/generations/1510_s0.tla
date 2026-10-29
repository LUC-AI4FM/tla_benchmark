----------------------------- MODULE J -----------------------------
EXTENDS Integers

VARIABLES x, y

vars == <<x, y>>

Foo(f) == IF x = 1 THEN [f EXCEPT ![x] = 42] ELSE f

Init == /\ x \in {1, 2, 3, 4, 5}
        /\ y = [i \in {1, 2, 3, 4, 5} |-> 0]

Next == /\ x' = x
        /\ y' = Foo(y)

Spec == Init /\ [][Next]_vars
=============================================================================