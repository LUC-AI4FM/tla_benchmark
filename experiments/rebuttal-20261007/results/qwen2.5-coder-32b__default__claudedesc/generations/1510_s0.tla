------------------------------- MODULE J -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Domain
VARIABLES x, y

ASSUME Domain = {1, 2, 3, 4, 5}

Init == /\ x \in Domain
        /\ y = [d \in Domain |-> 0]

Foo ==
    IF x = 1 THEN [y EXCEPT ![x] = 42]
    ELSE y

Next == \/ /\ UNCHANGED x
            /\ y' = Foo

Spec == Init /\ [][Next]_<<x, y>>

=============================================================================