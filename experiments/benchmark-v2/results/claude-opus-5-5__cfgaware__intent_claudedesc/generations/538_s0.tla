---------------------------- MODULE SquareByOdds ----------------------------
EXTENDS Naturals

CONSTANT NSet

ASSUME NSet \subseteq Nat

VARIABLES a, b, i, n, pc, x

vars == << a, b, i, n, pc, x >>

Init == /\ n \in NSet
        /\ x = 0
        /\ a = 1
        /\ b = 2
        /\ i = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i < n
               THEN /\ x' = x + a
                    /\ a' = a + b
                    /\ i' = i + 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, a, i >>
         /\ UNCHANGED << b, n >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == /\ n \in Nat
          /\ x \in Nat
          /\ a \in Nat
          /\ b = 2
          /\ i \in Nat
          /\ pc \in {"Lbl_1", "Done"}

LoopInvariant == /\ x = i * i
                 /\ a = 2 * i + 1
                 /\ i <= n

PartialCorrectness == (pc = "Done") => (x = n * n)

Termination == <>(pc = "Done")

=============================================================================