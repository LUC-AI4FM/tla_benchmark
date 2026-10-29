---------------------------- MODULE SimpleProgram ----------------------------
EXTENDS Integers, TLC

VARIABLES x, pc

vars == << x, pc >>

TypeOK == /\ x \in 1..10
          /\ pc \in {"A", "Done"}

Init == /\ x \in 1..10
        /\ pc = "A"

A == /\ pc = "A"
     /\ Assert(x * x <= 100, "Failure of assertion at line A.")
     /\ pc' = "Done"
     /\ UNCHANGED x

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == A \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

SquareBound == x * x <= 100

Safety == []SquareBound

=============================================================================