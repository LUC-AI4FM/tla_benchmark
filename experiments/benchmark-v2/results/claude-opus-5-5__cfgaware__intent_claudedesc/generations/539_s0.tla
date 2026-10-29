---------------------------- MODULE Squares ----------------------------
EXTENDS Naturals

CONSTANT NSet

ASSUME NSet \subseteq Nat

ConstNSet == {0, 2, 7}

VARIABLES n, a, i, pc

vars == <<n, a, i, pc>>

Init ==
    /\ n \in NSet
    /\ a = [j \in 0..n |-> 0]
    /\ i = 0
    /\ pc = "loop"

Step ==
    /\ pc = "loop"
    /\ a' = [a EXCEPT ![i] = i * i]
    /\ IF i = n
          THEN /\ pc' = "done"
               /\ i' = i
          ELSE /\ i' = i + 1
               /\ pc' = "loop"
    /\ UNCHANGED n

Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

TypeOK ==
    /\ n \in Nat
    /\ a \in [0..n -> 0..(n * n)]
    /\ i \in 0..n
    /\ pc \in {"loop", "done"}

SquareCorrect ==
    pc = "done" => \A j \in 0..n : a[j] = j * j

ReachableStateInv ==
    /\ TypeOK
    /\ pc = "loop" =>
          /\ \A j \in 0..n : j < i => a[j] = j * j
          /\ \A j \in 0..n : j >= i => a[j] = 0
    /\ pc = "done" =>
          /\ i = n
          /\ \A j \in 0..n : a[j] = j * j

=============================================================================