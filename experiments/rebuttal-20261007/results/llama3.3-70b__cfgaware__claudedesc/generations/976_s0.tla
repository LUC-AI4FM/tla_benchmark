---------------------------- MODULE SimpleConcurrentAlgorithm ----------------------------
EXTENDS Integers, TLC

CONSTANT N

VARIABLE x, y, pc

TypeOK == (* type correctness invariant *)
          /\ x \in [0..N-1 -> {0, 1}]
          /\ y \in [0..N-1 -> {0, 1}]
          /\ pc \in [0..N-1 -> {"a", "b", "Done"}]

Inv == (* inductive invariant *)
      /\ TypeOK
      /\ \A i \in 0..N-1 : pc[i] = "b" \/ pc[i] = "Done" => x[i] = 1
      /\ \E i \in 0..N-1 : pc[i] /= "Done" \/ \E j \in 0..N-1 : y[j] = 1

PCorrect == (* correctness property *)
            \A i \in 0..N-1 : pc[i] = "Done" => \E j \in 0..N-1 : y[j] = 1

Spec == (* specification *)
       /\ TypeOK
       /\ x = [i \in 0..N-1 |-> 0]
       /\ y = [i \in 0..N-1 |-> 0]
       /\ pc = [i \in 0..N-1 |-> "a"]
       /\ [][* (* next-state relation *)
           /\ \E i \in 0..N-1 :
               /\ pc[i] = "a"
               /\ x' = [x EXCEPT ![i] = 1]
               /\ y' = y
               /\ pc' = [pc EXCEPT ![i] = "b"]
               /\ \A j \in 0..N-1 : j /= i => pc'[j] = pc[j]
           \/ /\ \E i \in 0..N-1 :
               /\ pc[i] = "b"
               /\ y' = [y EXCEPT ![i] = x[(i-1) % N]]
               /\ x' = x
               /\ pc' = [pc EXCEPT ![i] = "Done"]
               /\ \A j \in 0..N-1 : j /= i => pc'[j] = pc[j]
           /\ \A i \in 0..N-1 : pc[i] = "Done" => pc'[i] = "Done"
           ]

THEOREM Spec => []PCorrect
PROOF (* proof using TLAPS *)
  <1>1. Inv => PCorrect
    BY DEF Inv, PCorrect
  <2>2. Spec => Inv
    BY DEF Spec, Inv
  <3>3. Inv => [][*]Inv
    SUFFICE TO PROVE Inv /\ [*] => Inv'
      <4> BY DEF Inv, TypeOK, pc
  QED

THEOREM Correctness2 == Spec => []Inv
PROOF (* concise proof using TLAPS *)
  Inv => [][*]Inv
    SUFFICE TO PROVE Inv /\ [*] => Inv'
      BY DEF Inv, TypeOK, pc
  QED
=============================================================================