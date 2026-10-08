----------------------------- MODULE EuclidAlgorithm -----------------------------

EXTENDS Naturals, TLC

CONSTANTS N

VARIABLES pc, u, v, v_ini

Init == /\ pc = "Start"
        /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v

Next ==
    CASE pc = "Start" ->
         /\ pc' = "Subtract"
         /\ u' = u - v
         /\ UNCHANGED <<v, v_ini>>
    [] pc = "Subtract" /\
       u >= v ->
         /\ pc' = "Subtract"
         /\ u' = u - v
         /\ UNCHANGED <<v, v_ini>>
    [] pc = "Subtract" /\
       u < v ->
         /\ pc' = "Swap"
         /\ UNCHANGED <<u, v_ini>>
         /\ v' = u
    [] pc = "Swap" ->
         /\ pc' = IF u = 0 THEN "Done" ELSE "Subtract"
         /\ UNCHANGED <<u, v>>
         
Spec ==
    /\ Init
    /\ [][Next]_<<pc, u, v, v_ini>>
    /\ WF_[Next]_<<pc, u, v, v_ini>>

Termination == <>[](pc = "Done")

=============================================================================