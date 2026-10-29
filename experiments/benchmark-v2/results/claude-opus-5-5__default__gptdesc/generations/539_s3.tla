---------------------------- MODULE MCSession6func ----------------------------
EXTENDS Naturals, TLC

CONSTANT n

ASSUME NAssump == n \in Nat

VARIABLES x, i, pc

vars == << x, i, pc >>

Init == /\ x = [k \in 0..n |-> 0]
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i <= n
           THEN pc' = "b"
           ELSE pc' = "Done"
     /\ UNCHANGED << x, i >>

b == /\ pc = "b"
     /\ x' = [x EXCEPT ![i] = i * i]
     /\ i' = i + 1
     /\ pc' = "a"

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------

Correct == pc = "Done" => \A j \in 0..n : x[j] = j * j

TypeOK == /\ n \in Nat
          /\ x \in [0..n -> Nat]
          /\ i \in 0..(n+1)
          /\ pc \in {"a", "b", "Done"}

Inv == /\ TypeOK
       /\ \A j \in 0..(i-1) : x[j] = j * j
       /\ pc = "a"    => i \in 0..(n+1)
       /\ pc = "b"    => i \in 0..n
       /\ pc = "Done" => i = n + 1

THEOREM Spec => [](TypeOK /\ Inv /\ Correct)
=============================================================================