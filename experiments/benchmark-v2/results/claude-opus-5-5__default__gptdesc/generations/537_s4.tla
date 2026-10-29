---------------------------- MODULE MCSession6 ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

ConstNat == 0 .. 10

ASSUME N \in ConstNat

VARIABLES x, i, pc

vars == << x, i, pc >>

Init == /\ x = 0
        /\ i = 0
        /\ pc = "lp"

Loop == /\ pc = "lp"
        /\ IF i < N
              THEN pc' = "a"
              ELSE pc' = "Done"
        /\ UNCHANGED << x, i >>

StepA == /\ pc = "a"
         /\ x' = x + 2 * i + 1
         /\ pc' = "b"
         /\ UNCHANGED i

StepB == /\ pc = "b"
         /\ i' = i + 1
         /\ pc' = "lp"
         /\ UNCHANGED x

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == Loop \/ StepA \/ StepB \/ Terminating

Spec == Init /\ [][Next]_vars

PartialCorrectness == (pc = "Done") => (x = N * N)

TypeOK == /\ x \in Nat
          /\ i \in Nat
          /\ pc \in {"lp", "a", "b", "Done"}

Inv == /\ TypeOK
       /\ (pc = "lp"   => /\ i \in 0 .. N
                          /\ x = i * i)
       /\ (pc = "a"    => /\ i \in 0 .. (N - 1)
                          /\ x = i * i)
       /\ (pc = "b"    => /\ i \in 0 .. (N - 1)
                          /\ x = (i + 1) * (i + 1))
       /\ (pc = "Done" => /\ i = N
                          /\ x = N * N)

THEOREM Spec => [](TypeOK /\ Inv /\ PartialCorrectness)
=============================================================================