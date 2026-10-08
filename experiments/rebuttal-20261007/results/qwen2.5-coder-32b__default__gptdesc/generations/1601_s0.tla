------------------------------- MODULE FischerTimedMutualExclusion -------------------------------
EXTENDS Naturals, TLC

CONSTANTS N, Delta, Epsilon, Infinity

VARIABLES requestTime, inCS, timer

Init == /\ requestTime = [p \in 1..N -> Infinity]
        /\ inCS = [p \in 1..N -> FALSE]
        /\ timer = [p \in 1..N -> Infinity]

Next ==
    \/ \E p \in 1..N : 
         /\ ~inCS[p]
         /\ requestTime' = [requestTime EXCEPT ![p] = <<CHOOSE t \in Nat : t > Max({requestTime[q] : q \in 1..N})>>]
         /\ inCS' = [inCS EXCEPT ![p] = TRUE]
         /\ timer' = [timer EXCEPT ![p] = Delta]
         /\ UNCHANGED <<requestTime EXCEPT ![p], inCS EXCEPT ![p], timer EXCEPT ![p]>>
    \/ \E p \in 1..N : 
         /\ inCS[p]
         /\ requestTime' = requestTime
         /\ inCS' = [inCS EXCEPT ![p] = FALSE]
         /\ timer' = [timer EXCEPT ![p] = Infinity]
         /\ UNCHANGED <<requestTime EXCEPT ![p], inCS EXCEPT ![p], timer EXCEPT ![p]>>
    \/ \E p \in 1..N : 
         /\ ~inCS[p]
         /\ requestTime'[p] = requestTime[p]
         /\ inCS'[p] = FALSE
         /\ timer'[p] = [IF timer[p] > Epsilon THEN timer[p] - Epsilon ELSE 0]
         /\ UNCHANGED <<requestTime EXCEPT ![p], inCS EXCEPT ![p], timer EXCEPT ![p]>>

Spec == Init /\ [][Next]_<<requestTime, inCS, timer>>

MutualExclusion == \A p, q \in 1..N : p # q => ~(\E t \in Nat : inCS[p][t] /\ inCS[q][t])

Liveness == <>[] (\E p \in 1..N : <>(inCS[p]))

Fairness ==
    WF_next(<<requestTime, inCS, timer>>)

THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness

CONSTRAINT Fairness

=============================================================================