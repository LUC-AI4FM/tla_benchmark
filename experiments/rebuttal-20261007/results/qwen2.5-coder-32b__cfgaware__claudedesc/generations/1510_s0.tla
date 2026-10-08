---- MODULE J ----

CONSTANTS
    \* No additional constants are needed for this specification

VARIABLES
    x,
    y

Foo ==
    IF x = 1 THEN [y EXCEPT ![x] = 42]
    ELSE y

Next ==
    /\ UNCHANGED x
    /\ y' = Foo

Init ==
    /\ x \in {1, 2, 3, 4, 5}
    /\ y = [k \in {1, 2, 3, 4, 5} |-> 0]

Spec ==
    Init /\ [][Next]_<<x, y>>

====