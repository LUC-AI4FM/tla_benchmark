---------------------------- MODULE MCSession6 ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

\* Concrete constant set used for model checking
NValues == 0..5

ASSUME N \in NValues

VARIABLES x, i, pc

vars == << x, i, pc >>

\* Specification as given in Session6 (computing N*N by repeated addition)

Init == /\ x = 0
        /\ i = 0
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ IF i < N
            THEN pc' = "l2"
            ELSE pc' = "Done"
      /\ UNCHANGED << x, i >>

l2 == /\ pc = "l2"
      /\ x' = x + N
      /\ pc' = "l3"
      /\ UNCHANGED i

l3 == /\ pc = "l3"
      /\ i' = i + 1
      /\ pc' = "l1"
      /\ UNCHANGED x

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == l1 \/ l2 \/ l3 \/ Terminating

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Model-checking properties

\* Partial correctness: if the program has terminated, x holds the square of N
PartialCorrectness == (pc = "Done") => (x = N * N)

\* Typing invariant over the state variables
TypeOK == /\ x \in Nat
          /\ i \in Nat
          /\ pc \in {"l1", "l2", "l3", "Done"}

\* Stronger inductive invariant characterizing reachable states
Inv == /\ TypeOK
       /\ (pc = "l1")   => (x = i * N /\ i <= N)
       /\ (pc = "l2")   => (x = i * N /\ i < N)
       /\ (pc = "l3")   => (x = (i + 1) * N /\ i < N)
       /\ (pc = "Done") => (x = N * N /\ i = N)

THEOREM Spec => [](TypeOK /\ Inv /\ PartialCorrectness)
=============================================================================