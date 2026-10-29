---------------------------- MODULE MC_Session6 ----------------------------
EXTENDS Naturals

CONSTANT NSet

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

ConstNSet == {2, 7, 0}

(* Iterative squaring:
   a: if i < n then i := i + 1; goto b else goto Done
   b: x := x + 2*i - 1; goto a                         *)

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
     /\ x' = x + 2 * i - 1
     /\ pc' = "a"
     /\ UNCHANGED << n, i >>

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == /\ n \in Nat
          /\ x \in 0..(n * n)
          /\ i \in 0..n
          /\ pc \in {"a", "b", "Done"}

SquareCorrect == pc = "Done" => x = n * n

ReachableStateInv ==
    /\ TypeOK
    /\ pc = "a"    => x = i * i
    /\ pc = "b"    => /\ i > 0
                      /\ x = (i - 1) * (i - 1)
    /\ pc = "Done" => /\ x = n * n
                      /\ i = n

=============================================================================