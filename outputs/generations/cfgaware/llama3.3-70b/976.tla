--------------------------- MODULE RingAlgorithm ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE x, y, pc

TypeOK == (/\
  /\ x \in [1..N -> Nat]
  /\ y \in [1..N -> Nat]
  /\ pc \in [1..N -> Int])

Inv == TypeOK /\ 
       (\* inductive invariant: at least one process has not started or is done *)
       (\E i \in 1..N : pc[i] = 0 \/ pc[i] = 2)

Init == (/\
  /\ x = [i \in 1..N |-> 1]
  /\ y = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> 0])

Next == (\E i \in 1..N :
           /\ pc[i] = 0
           /\ x' = [x EXCEPT ![i] = 1]
           /\ y' = y
           /\ pc' = [pc EXCEPT ![i] = 1]
         \/ 
           /\ pc[i] = 1
           /\ x' = x
           /\ y' = [y EXCEPT ![i] = x[(i-1 # N) + 1]]
           /\ pc' = [pc EXCEPT ![i] = 2]
         \/ 
           /\ pc[i] = 2
           /\ UNCHANGED <<x, y, pc>>)

Spec == Init /\ [][Next]_<<x, y, pc>>

PCorrect == <>(\A i \in 1..N : pc[i] = 2)

THEOREM Spec => []TypeOK
PROOF * TLAPS

THEOREM Spec => PCorrect
PROOF * TLAPS

THEOREM Spec => []Inv
PROOF * TLAPS

THEOREM Spec => [](PCorrect => \E i \in 1..N : y[i] = 1)
PROOF * TLAPS
=============================================================================