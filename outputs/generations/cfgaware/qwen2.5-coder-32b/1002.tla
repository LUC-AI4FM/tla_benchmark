------------------------------- MODULE BarrierSync -------------------------------

CONSTANTS N

VARIABLES pc

(* --algorithm BarrierSync
variables pc = [p \in 1..N -> "b0"];

next ==
    /\ \/ /\ pc[self] = "b0"
           /\ pc' = [pc EXCEPT ![self] = "b1"]
       \/ /\ pc[self] = "b1"
           /\ (\A p \in 1..N: pc[p] = "b1")
           /\ pc' = [p \in 1..N -> "b0"]

TypeOK ==
    /\ pc \in [1..N -> {"b0", "b1"}]

BarrierProperty ==
    \A p \in 1..N, s \in State: 
        \/ pc[s][p] # "b1"
        \/ (\A q \in 1..N: pc[s][q] = "b1")

Spec ==
    /\ TypeOK
    /\ WF_next(pc)

end algorithm *)

=============================================================================