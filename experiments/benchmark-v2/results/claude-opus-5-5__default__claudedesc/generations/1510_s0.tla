---- MODULE J ----
EXTENDS Integers

VARIABLES x, y

vars == <<x, y>>

Foo(r) == IF x = 1 THEN [r EXCEPT ![x] = 42] ELSE r

Init == /\ x \in {1, 2, 3, 4, 5}
        /\ y = [i \in {1, 2, 3, 4, 5} |-> 0]

Next == /\ x' = x
        /\ y' = Foo(y)

Spec == Init /\ [][Next]_vars
====