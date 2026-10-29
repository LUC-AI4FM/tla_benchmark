---------------------------- MODULE OddSquares ----------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT NSet

ASSUME NSet \subseteq Nat

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init == /\ n \in NSet
        /\ x = [j \in 0..n |-> 0]
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < n
           THEN /\ i' = i + 1
                /\ x' = [x EXCEPT ![i + 1] = x[i] + (2 * (i + 1) - 1)]
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << x, i >>
     /\ n' = n

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------
(* Additional safety properties *)

TypeOK == /\ n \in NSet
          /\ x \in [0..n -> Nat]
          /\ i \in 0..n
          /\ pc \in {"a", "Done"}

SquaresCorrect == \A k \in 0..i : x[k] = k * k

ResultCorrect == (pc = "Done") => (x[n] = n * n)

=============================================================================