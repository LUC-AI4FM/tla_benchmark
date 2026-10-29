---- MODULE IntegerExponentiation ----
EXTENDS Integers, Naturals, TLC

CONSTANTS MSet, NSet

ASSUME MSet \subseteq Int
ASSUME NSet \subseteq Nat

VARIABLES m, n, res, i, pc

vars == << m, n, res, i, pc >>

Init == /\ m \in MSet
        /\ n \in NSet
        /\ res = 1
        /\ i = 1
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(m \in Int /\ n \in Nat,
                   "Failure of assertion at line 1: inputs not well typed")
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << m, n, res, i >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i <= n
               THEN /\ res' = res * m
                    /\ i' = i + 1
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(res = m ^ n,
                              "Failure of assertion: res # m^n")
                    /\ pc' = "Done"
                    /\ UNCHANGED << res, i >>
         /\ UNCHANGED << m, n >>

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

====