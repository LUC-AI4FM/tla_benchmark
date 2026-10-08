----------------------------- MODULE PlusCalExample -----------------------------
EXTENDS Naturals

VARIABLES x, pc

Init ==
    /\ x \in 1..10
    /\ pc = "Start"

Next ==
    \/ /\ pc = "Start"
       /\ x ^ 2 <= 100
       /\ pc' = "Done" /\ x' = x
    \/ /\ pc = "Done"
       /\ pc' = "Done" /\ x' = x

Spec == Init /\ [] Next

SafetyInv ==
    /\ x \in 1..10
    /\ pc \in {"Start","Done"}
    /\ x ^ 2 <= 100

Termination == <> (pc = "Done")

=============================================================================