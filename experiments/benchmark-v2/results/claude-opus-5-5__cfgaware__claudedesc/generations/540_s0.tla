---------------------------- MODULE OddSquares ----------------------------
EXTENDS Integers, Naturals, TLC

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

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK == /\ n \in NSet
          /\ i \in 0..n
          /\ x \in [0..n -> Nat]
          /\ pc \in {"a", "Done"}

Correct == \A j \in 0..i : x[j] = j * j

=============================================================================