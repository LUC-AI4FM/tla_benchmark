------------------------------ MODULE FischerTimedMutex ------------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS N, Delta, Epsilon, Infinity

VARIABLES requestTime, inCS, timer

Init == 
  /\ requestTime = [p \in 1..N -> Infinity]
  /\ inCS = [p \in 1..N -> FALSE]
  /\ timer = [p \in 1..N -> 0]

Next ==
  \/ \E p \in 1..N :: 
      (\* Requesting critical section *)
      /\ inCS[p] = FALSE
      /\ requestTime' = [requestTime EXCEPT ![p] = <<CHOOSE t \in Nat : t > requestTime[p]>>]
      /\ UNCHANGED <<inCS, timer>>
  \/ \E p \in 1..N :: 
      (\* Entering critical section *)
      /\ inCS[p] = FALSE
      /\ \A q \in 1..N \ {p} : (requestTime[q] = Infinity \/ requestTime[p] < requestTime[q] \/ (requestTime[p] = requestTime[q] /\ p < q))
      /\ timer' = [timer EXCEPT ![p] = Delta]
      /\ inCS' = [inCS EXCEPT ![p] = TRUE]
      /\ UNCHANGED <<requestTime, [q \in 1..N \ {p} -> timer[q]]>>
  \/ \E p \in 1..N :: 
      (\* Exiting critical section *)
      /\ inCS[p] = TRUE
      /\ timer' = [timer EXCEPT ![p] = 0]
      /\ inCS' = [inCS EXCEPT ![p] = FALSE]
      /\ UNCHANGED <<requestTime, [q \in 1..N \ {p} -> timer[q]]>>
  \/ \* Ticking process *)
     /\ \E p \in 1..N :: 
        (\* Decrementing timer *)
        /\ inCS[p] = FALSE
        /\ timer[p] > 0
        /\ timer' = [timer EXCEPT ![p] = timer[p] - Epsilon]
        /\ UNCHANGED <<requestTime, [q \in 1..N \ {p} -> timer[q]], inCS>>

Spec ==
  Init /\ [][Next]_<<requestTime, inCS, timer>>
  
(\* Mutual exclusion invariant *)
MutualExclusion == 
  \/ \A p \in 1..N : inCS[p] = FALSE
  \/ \E p \in 1..N : inCS[p] = TRUE /\ \A q \in 1..N \ {p} : inCS[q] = FALSE

(\* Liveness property: some process is infinitely often in the critical section *)
Liveness == 
  <>[] (\E p \in 1..N : inCS[p] = TRUE)

(\* Fairness conditions *)
Fairness ==
  WF_next(\A p \in 1..N :: <p, "request">)
  
THEOREM Spec => []MutualExclusion
THEOREM Spec /\ Fairness => Liveness

=============================================================================