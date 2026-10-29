--------------------------- MODULE IterativeExponentiation ---------------------------
EXTENDS Naturals, Integers, TLC

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
         /\ IF i =< n
               THEN /\ res' = res * m
                    /\ i' = i + 1
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(res = m ^ n,
                              "Failure of assertion: res = m ^ n")
                    /\ pc' = "Done"
                    /\ UNCHANGED << res, i >>
         /\ UNCHANGED << m, n >>

(* Allow infinite stuttering after termination to prevent deadlock. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

(* Safety properties *)
TypeOK == /\ m \in MSet
          /\ n \in NSet
          /\ res \in Int
          /\ i \in Nat
          /\ pc \in {"Lbl_1", "Done"}

LoopInvariant == (pc = "Lbl_1") => (i \in 1..(n + 1) /\ res = m ^ (i - 1))

Correctness == (pc = "Done") => (res = m ^ n)

=====================================================================================