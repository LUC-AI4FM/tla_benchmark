------------------------------ MODULE Counter ------------------------------
EXTENDS Naturals

VARIABLE c

Init == c = 0

Increment ==
    /\ c < 10
    /\ c' = c + 1

Next == Increment

Spec == Init /\ WF_vars(Increment) /\ [][Next]_c

Termination == <> (c = 10)

=============================================================================