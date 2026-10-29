---- MODULE Square ----
EXTENDS Naturals

CONSTANT NSet

ASSUME NSet \subseteq Nat

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init == /\ n \in NSet
        /\ x = 0
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < n
           THEN /\ i' = i + 1
                /\ pc' = "b"
           ELSE /\ pc' = "Done"
                /\ i' = i
     /\ UNCHANGED << n, x >>

b == /\ pc = "b"
     /\ x' = x + (2 * i) - 1
     /\ pc' = "a"
     /\ UNCHANGED << n, i >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

====