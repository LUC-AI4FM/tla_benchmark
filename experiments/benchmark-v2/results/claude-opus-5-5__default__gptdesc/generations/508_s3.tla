---- MODULE SquareAssert ----
EXTENDS Integers, TLC

VARIABLES x, pc

vars == << x, pc >>

Init == /\ x \in 1..10
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(x ^ 2 <= 100, "Failure of assertion at line 6, column 5.")
         /\ pc' = "Done"
         /\ x' = x

Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK == /\ x \in 1..10
          /\ pc \in {"Lbl_1", "Done"}

SquareBound == x ^ 2 <= 100

====