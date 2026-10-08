------------------------------- MODULE FischerTimedMutualExclusion -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, Delta, Epsilon, Infinity
ASSUME /\ N \in Nat
       /\ N > 1
       /\ Delta \in Nat
       /\ Epsilon \in Nat
       /\ Delta >= Epsilon

VARIABLES requestTime, lastUsed, timer, inCS, turn

Init == /\ requestTime = [i \in 1..N -> Infinity]
        /\ lastUsed = 0
        /\ timer = [i \in 1..N -> Infinity]
        /\ inCS = FALSE
        /\ turn = 0

Next ==
    \/ /\ \/ \E i \in 1..N : \/ ~inCS /\ requestTime[i] = lastUsed + Epsilon
                              /\ (\/ turn = i
                                  \/ (\A j \in 1..N : timer[j] > requestTime[i]))
                          -> ['][[requestTime' = [requestTime EXCEPT ![i] = lastUsed + Delta],
                                 timer' = [timer EXCEPT ![j \in 1..N | j # i] = timer[j]],
                                 inCS' = TRUE,
                                 turn' = i]]
       \/ /\ inCS
          -> ['][[inCS' = FALSE, 
                 lastUsed' = requestTime[turn]]]
       \/ /\ \E i \in 1..N : timer[i] > Epsilon
          -> ['][[timer' = [timer EXCEPT ![i] = timer[i] - Epsilon]]]

Spec == Init /\ [][Next]_<<requestTime, lastUsed, timer, inCS, turn>>

\* Mutual Exclusion Invariant: At most one process is in the critical section
MutualExclusion == \/ ~inCS \/ \A i \in 1..N : requestTime[i] # lastUsed + Epsilon

\* Liveness Property: Some process is infinitely often in the critical section
Fairness ==
    /\ WF_<<requestTime, lastUsed, timer, inCS, turn>>(Next)
    /\ SF_<<requestTime, lastUsed, timer, inCS, turn>>(inCS)

THEOREM Spec => []MutualExclusion

THEOREM Spec /\ Fairness => <>[]inCS

=============================================================================