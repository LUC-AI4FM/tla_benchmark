---- MODULE Exercise ----
EXTENDS Naturals, TLC

VARIABLES x, pc

vars == << x, pc >>

Init == /\ x \in 1..10
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(x * x <= 100, "Failure of assertion at line 6, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED x

Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

====