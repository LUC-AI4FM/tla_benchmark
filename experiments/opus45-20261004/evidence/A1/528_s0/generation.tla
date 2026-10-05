---------------------------- MODULE Specification ----------------------------

EXTENDS Integers, Sequences, TLC

VARIABLES x, y, pc

vars == <<x, y, pc>>

Init ==
    /\ x = {"a", "b"}
    /\ y = <<1, 2, 3>>
    /\ pc = "start"

Step ==
    /\ pc = "start"
    /\ x' = x \union {"c"}
    /\ y' = <<y[1], 4, y[3]>>
    /\ PrintT(x')
    /\ PrintT(y')
    /\ pc' = "Done"

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Step
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

=============================================================================