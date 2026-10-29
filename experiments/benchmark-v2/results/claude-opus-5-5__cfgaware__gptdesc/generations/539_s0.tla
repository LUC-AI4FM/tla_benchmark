---------------------------- MODULE MCSession6func ----------------------------
EXTENDS Naturals, TLC

CONSTANT NSet

ASSUME NSet \subseteq Nat

ConstNSet == 0..4

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

Init ==
    /\ n \in NSet
    /\ x = [j \in 0..n |-> 0]
    /\ i = 0
    /\ pc = "a"

a ==
    /\ pc = "a"
    /\ IF i <= n
          THEN pc' = "b"
          ELSE pc' = "Done"
    /\ UNCHANGED << n, x, i >>

b ==
    /\ pc = "b"
    /\ x' = [x EXCEPT ![i] = i * i]
    /\ i' = i + 1
    /\ pc' = "a"
    /\ UNCHANGED n

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

SquareCorrect ==
    (pc = "Done") => (\A j \in 0..n : x[j] = j * j)

TypeOK ==
    /\ n \in Nat
    /\ n \in NSet
    /\ x \in [0..n -> Nat]
    /\ i \in 0..(n + 1)
    /\ pc \in {"a", "b", "Done"}

DoneUpTo(k) == \A j \in 0..(k - 1) : x[j] = j * j

ZeroFrom(k) == \A j \in k..n : x[j] = 0

ReachableStateInv ==
    /\ TypeOK
    /\ (pc = "a") =>
          /\ i \in 0..(n + 1)
          /\ DoneUpTo(i)
          /\ ZeroFrom(i)
    /\ (pc = "b") =>
          /\ i \in 0..n
          /\ DoneUpTo(i)
          /\ ZeroFrom(i)
    /\ (pc = "Done") =>
          /\ i = n + 1
          /\ \A j \in 0..n : x[j] = j * j

=============================================================================