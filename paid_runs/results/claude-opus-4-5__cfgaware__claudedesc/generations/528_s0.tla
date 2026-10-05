---------------------------- MODULE Specification ----------------------------
EXTENDS Naturals, Sequences, TLC

VARIABLES x, y, pc

vars == <<x, y, pc>>

Init ==
    /\ x = {"a", "b"}
    /\ y = <<1, 2, 3>>
    /\ pc = "start"

Lbl_1 ==
    /\ pc = "start"
    /\ x' = x \union {"c"}
    /\ y' = [y EXCEPT ![2] = 4]
    /\ PrintT(x')
    /\ PrintT(y')
    /\ pc' = "Done"

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Lbl_1
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

=============================================================================