---------------------------- MODULE Session6func ----------------------------
EXTENDS Naturals

CONSTANT NSet

ASSUME NSet \subseteq Nat

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init ==
    /\ n \in NSet
    /\ x = [j \in 0..n |-> 0]
    /\ i = 0
    /\ pc = "a"

a ==
    /\ pc = "a"
    /\ IF i < n
         THEN /\ i' = i + 1
              /\ pc' = "b"
         ELSE /\ pc' = "Done"
              /\ i' = i
    /\ UNCHANGED << n, x >>

b ==
    /\ pc = "b"
    /\ x' = [x EXCEPT ![i] = x[i - 1] + 2 * i - 1]
    /\ pc' = "a"
    /\ UNCHANGED << n, i >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

ConstNSet == {2, 7, 0}

TypeOK ==
    /\ n \in Nat
    /\ x \in [0..n -> 0..(n * n)]
    /\ i \in 0..n
    /\ pc \in {"a", "b", "Done"}

SquareCorrect ==
    pc = "Done" => \A j \in 0..n : x[j] = j * j

ReachableStateInv ==
    /\ (pc = "a") =>
          /\ x[i] = i * i
          /\ \A j \in 0..i : x[j] = j * j
    /\ (pc = "b") =>
          /\ i > 0
          /\ x[i - 1] = (i - 1) * (i - 1)
          /\ \A j \in 0..(i - 1) : x[j] = j * j
    /\ (pc = "Done") =>
          /\ \A j \in 0..n : x[j] = j * j
          /\ i = n

=============================================================================