---------------------------- MODULE Squares ----------------------------
EXTENDS Naturals

CONSTANT NSet

ASSUME NSet \subseteq Nat

(***************************************************************************
--algorithm Squares {
    variables n \in NSet, x = 0, i = 0;
    {
      a: while (i < n) {
           i := i + 1;
           x := x + 2*i - 1
         }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init == (* Global variables *)
        /\ n \in NSet
        /\ x = 0
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < n
           THEN /\ i' = i + 1
                /\ x' = x + 2*(i + 1) - 1
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << x, i >>
     /\ n' = n

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

TypeOK == /\ n \in NSet
          /\ x \in Nat
          /\ i \in Nat
          /\ pc \in {"a", "Done"}

Correctness == (pc = "Done") => (x = n * n)

LoopInv == /\ x = i * i
           /\ i <= n

THEOREM Spec => []TypeOK /\ []Correctness /\ Termination
=============================================================================