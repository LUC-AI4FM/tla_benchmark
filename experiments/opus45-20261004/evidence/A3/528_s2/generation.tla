---------------------------- MODULE Specification ----------------------------
EXTENDS Sequences, FiniteSets, TLC

VARIABLES x, y, pc

vars == <<x, y, pc>>

Init ==
    /\ x = {"a", "b"}
    /\ y = <<1, 2, 3>>
    /\ pc = "start"

Step ==
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
    \/ Step
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

TypeInvariant ==
    /\ x \subseteq {"a", "b", "c"}
    /\ y \in Seq(Int)
    /\ Len(y) = 3
    /\ pc \in {"start", "Done"}

=============================================================================