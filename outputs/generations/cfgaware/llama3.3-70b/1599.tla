---------------------------- MODULE FastMutualExclusion ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE x, y, b, pc

Invariant == \A i, j \in 1..N : i # j => pc[i] # "CS" \/ pc[j] # "CS"

CondLiveness == \A i \in 1..N : <>pc[i] = "CS"

FairSpec == /\ []Invariant
             /\ WF_vars({x, y, b}, {<<i, "NCS">> : i \in 1..N})
             /\ WF_vars({x, y, b}, {<<i, "Try">> : i \in 1..N})
             /\ WF_vars({x, y, b}, {<<i, "Exit">> : i \in 1..N})

TypeOK == x \in (1..N) \cup {0}
       /\ y \in (1..N) \cup {0}
       /\ b \in [1..N -> BOOLEAN]
       /\ pc \in [1..N -> {"NCS", "Try", "CS", "Exit"}]

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ pc = [i \in 1..N |-> "NCS"]

Next == \E i \in 1..N : pc[i] = "NCS" /\ pc' = [pc EXCEPT ![i] = "Try"]
             \/ pc[i] = "Try" /\ x = 0 /\ x' = i /\ y' = i /\ b' = [b EXCEPT ![i] = TRUE] /\ pc' = pc
             \/ pc[i] = "Try" /\ x = i /\ y # i /\ y' = i /\ b' = b /\ pc' = pc
             \/ pc[i] = "Try" /\ x = i /\ y = i /\ \A j \in 1..N : ~(b[j] /\ j # i) /\ x' = 0 /\ y' = 0 /\ b' = [b EXCEPT ![i] = FALSE] /\ pc' = [pc EXCEPT ![i] = "CS"]
             \/ pc[i] = "CS" /\ pc' = [pc EXCEPT ![i] = "Exit"]
             \/ pc[i] = "Exit" /\ x' = 0 /\ y' = 0 /\ b' = [b EXCEPT ![i] = FALSE] /\ pc' = [pc EXCEPT ![i] = "NCS"]

Spec == Init /\ [][Next]_<<x, y, b, pc>>
=============================================================================