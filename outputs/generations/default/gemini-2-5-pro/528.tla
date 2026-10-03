---- MODULE SmallAlgorithm ----
EXTENDS TLC, Sequences, FiniteSets

VARIABLES x, y, pc

vars == <<x, y, pc>>

Init ==
    /\ x = {"a", "b"}
    /\ y = <<1, 2, 3>>
    /\ pc = "Lbl_1"

\* The single step of the algorithm
Step ==
    /\ pc = "Lbl_1"
    /\ x' = x \cup {"c"}
    /\ y' = [y EXCEPT ![2] = 4]
    /\ PrintT(<x', y'>)
    /\ pc' = "Done"

\* A stuttering step when the algorithm is finished
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Step
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

================================