---------------------------- MODULE SquareByOdds ----------------------------
EXTENDS Naturals, TLC

CONSTANT NSet

ASSUME NSet \subseteq Nat

(***************************************************************************
--algorithm SquareByOdds {
    variables n \in NSet, x = 0, i = 0;
    {
      Lbl_1: while (i < n) {
               i := i + 1;
               x := x + 2*i - 1
             }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init == /\ n \in NSet
        /\ x = 0
        /\ i = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF i < n
               THEN /\ i' = i + 1
                    /\ x' = x + 2*(i + 1) - 1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, i >>
         /\ n' = n

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

TypeOK == /\ n \in Nat
          /\ x \in Nat
          /\ i \in Nat
          /\ pc \in {"Lbl_1", "Done"}

LoopInvariant == /\ x = i * i
                 /\ i <= n

Correctness == (pc = "Done") => (x = n * n)

=============================================================================