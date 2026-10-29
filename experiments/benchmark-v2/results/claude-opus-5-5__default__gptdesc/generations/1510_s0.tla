---- MODULE FooSpec ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

Foo(f, v) == IF v = 1 THEN [f EXCEPT ![v] = 42] ELSE f

Init == /\ x \in 1..5
        /\ y = [i \in {1, 2, 3, 4, 5} |-> 0]

Next == /\ y' = Foo(y, x)
        /\ x' = x

Spec == Init /\ [][Next]_vars

TypeOK == /\ x \in 1..5
          /\ y \in [{1, 2, 3, 4, 5} -> {0, 42}]

====