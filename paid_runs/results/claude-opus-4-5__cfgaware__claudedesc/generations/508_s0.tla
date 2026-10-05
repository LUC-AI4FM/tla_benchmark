---------------------------- MODULE specification ----------------------------

EXTENDS Integers

VARIABLES x, pc

vars == <<x, pc>>

Init ==
    /\ x \in 1..10
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ Assert(x * x <= 100, "Assertion failed: x^2 <= 100")
    /\ pc' = "Done"
    /\ x' = x

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Lbl_1
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

Assert(cond, msg) == cond

=============================================================================