---------------------------- MODULE Square ----------------------------
EXTENDS Naturals

CONSTANT NSet

ASSUME NSet \subseteq Nat

ConstNSet == 0..4

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init ==
    /\ n \in NSet
    /\ x = 0
    /\ i = 0
    /\ pc = "Loop"

Loop ==
    /\ pc = "Loop"
    /\ IF i < n
         THEN /\ x' = x + i + i + 1
              /\ i' = i + 1
              /\ pc' = "Loop"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED << x, i >>
    /\ UNCHANGED n

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Loop \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

SquareCorrect == (pc = "Done") => (x = n * n)

TypeOK ==
    /\ n \in Nat
    /\ x \in 0..(n * n)
    /\ i \in 0..n
    /\ pc \in {"Loop", "Done"}

ReachableStateInv ==
    /\ TypeOK
    /\ x = i * i
    /\ (pc = "Done") => (i = n /\ x = n * n)

=============================================================================