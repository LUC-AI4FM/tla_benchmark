---------------------------- MODULE spec ----------------------------
EXTENDS Integers

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x \in 1..10
    /\ pc = "start"

Next ==
    \/ /\ pc = "start"
       /\ Assert(x ^ 2 <= 100, "Assertion failed: x ^ 2 <= 100")
       /\ pc' = "Done"
       /\ x' = x
    \/ /\ pc = "Done"
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

=============================================================================