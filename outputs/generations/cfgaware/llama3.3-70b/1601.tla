--------------------------- MODULE Fischer --------------------------------
EXTENDS Integers, TLC

CONSTANT N, Epsilon, Delta, Infinity

VARIABLES timer, pc, critical

Spec == 
  /\ timer = [i \in 1..N |-> Infinity]
  /\ pc = [i \in 1..N |-> "idle"]
  /\ critical = << >>
  /\ [][
      \/ \E i \in 1..N : 
        /\ pc[i] = "idle"
        /\ timer[i] = Infinity
        /\ pc' = [pc EXCEPT ![i] = "try"]
        /\ timer' = timer
        /\ critical' = critical
      \/ \E i \in 1..N : 
        /\ pc[i] = "try"
        /\ timer[i] > Epsilon
        /\ pc' = [pc EXCEPT ![i] = "wait"]
        /\ timer' = [timer EXCEPT ![i] = timer[i] - Delta]
        /\ critical' = critical
      \/ \E i \in 1..N : 
        /\ pc[i] = "wait"
        /\ timer[i] <= Epsilon
        /\ pc' = [pc EXCEPT ![i] = "crit"]
        /\ timer' = timer
        /\ critical' = critical \cup {i}
      \/ \E i \in 1..N : 
        /\ pc[i] = "crit"
        /\ pc' = [pc EXCEPT ![i] = "exit"]
        /\ timer' = timer
        /\ critical' = critical \ {i}
      \/ \E i \in 1..N : 
        /\ pc[i] = "exit"
        /\ pc' = [pc EXCEPT ![i] = "idle"]
        /\ timer' = [timer EXCEPT ![i] = Infinity]
        /\ critical' = critical
      \/ \A i \in 1..N : 
        /\ pc'[i] = pc[i]
        /\ timer'[i] = IF timer[i] > Delta THEN timer[i] - Delta ELSE 0
        /\ critical' = critical
    ]

Invariant == 
  /\ \A i, j \in 1..N : i # j => pc[i] # "crit" \/ pc[j] # "crit"
  /\ \A i \in 1..N : pc[i] = "crit" => timer[i] > Epsilon

Liveness == <>[](\E i \in 1..N : pc[i] = "crit")

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
=============================================================================