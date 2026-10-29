---------------------------- MODULE Session6Props ----------------------------
EXTENDS Naturals

CONSTANT NSet

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

ConstNSet == 0..5

Init == /\ n \in NSet
        /\ x = 0
        /\ i = 0
        /\ pc = "Loop"

Loop == /\ pc = "Loop"
        /\ IF i < n
              THEN /\ x' = x + n
                   /\ i' = i + 1
                   /\ pc' = "Loop"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << x, i >>
        /\ UNCHANGED n

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == Loop \/ Terminating

Spec == Init /\ [][Next]_vars

SquareCorrect == (pc = "Done") => (x = n * n)

TypeOK == /\ n \in NSet
          /\ x \in Nat
          /\ i \in Nat
          /\ pc \in {"Loop", "Done"}

ReachableStateInv ==
    /\ TypeOK
    /\ (pc = "Loop") => /\ i \in 0..n
                        /\ x = i * n
    /\ (pc = "Done") => /\ i = n
                        /\ x = n * n
=============================================================================