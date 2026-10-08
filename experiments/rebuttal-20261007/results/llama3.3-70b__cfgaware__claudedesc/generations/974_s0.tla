---------------------------- MODULE RegularRegisters ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE x, y, pc

TypeOK == 
  /\ x \in [0..N-1 -> SUBSET {0, 1}]
  /\ y \in [0..N-1 -> {0, 1}]
  /\ pc \in [0..N-1 -> {"a1", "a2", "b", "Done"}]

Inv == 
  /\ TypeOK
  /\ \A i \in 0..N-1 : pc[i] \in {"b", "Done"} => x[i] = {1}
  /\ \E i \in 0..N-1 : pc[i] /= "Done" \/ y[i] = 1

PCorrect == 
  \A i \in 0..N-1 : pc[i] = "Done" => \E j \in 0..N-1 : y[j] = 1

Spec == 
  /\ TypeOK
  /\ \A i \in 0..N-1 : x[i] = {0}
  /\ \A i \in 0..N-1 : pc[i] = "a1"
  * [][
      \/ \E i \in 0..N-1 : 
          /\ pc[i] = "a1"
          /\ pc' = [pc EXCEPT ![i] = "a2"]
          /\ x' = [x EXCEPT ![i] = {0, 1}]
          /\ y' = y
      \/ \E i \in 0..N-1 : 
          /\ pc[i] = "a2"
          /\ pc' = [pc EXCEPT ![i] = "b"]
          /\ x' = [x EXCEPT ![i] = {1}]
          /\ y' = y
      \/ \E i \in 0..N-1 : 
          /\ pc[i] = "b"
          /\ pc' = [pc EXCEPT ![i] = "Done"]
          /\ x' = x
          /\ \E v \in x[(i-1) % N] : y' = [y EXCEPT ![i] = v]
      \/ \A i \in 0..N-1 : pc' = pc /\ x' = x /\ y' = y
    ]

THEOREM Spec => []PCorrect
PROOF * Inv *

THEOREM Spec => []Inv
PROOF * TypeOK *
=============================================================================