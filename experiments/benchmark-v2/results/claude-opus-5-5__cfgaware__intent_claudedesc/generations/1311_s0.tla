---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

VARIABLES u, v, pc

vars == << u, v, pc >>

Init == /\ u = 24
        /\ v \in 1..50
        /\ pc = "Lbl_1"

\* Loop test: while u # 0
Lbl_1 == /\ pc = "Lbl_1"
         /\ IF u # 0
               THEN pc' = "Lbl_2"
               ELSE pc' = "Done"
         /\ UNCHANGED << u, v >>

\* Loop body: if u < v then swap; then u := u - v
Lbl_2 == /\ pc = "Lbl_2"
         /\ IF u < v
               THEN /\ u' = v - u
                    /\ v' = u
               ELSE /\ u' = u - v
                    /\ v' = v
         /\ pc' = "Lbl_1"

\* Allow stuttering once done so the finished state is not a deadlock
Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

TypeOK == /\ u \in Nat
          /\ v \in Nat
          /\ pc \in {"Lbl_1", "Lbl_2", "Done"}

Termination == <>(pc = "Done")

=============================================================================