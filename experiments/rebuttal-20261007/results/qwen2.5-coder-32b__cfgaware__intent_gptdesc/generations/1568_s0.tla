------------------------------- MODULE BakeryAlgorithm -------------------------------

CONSTANTS NumProcs, MaxTicket \* Number of processes and upper bound on ticket values

VARIABLES choosing, number, inCS

\* Initialization predicate
Init == /\ choosing = [p \in 1..NumProcs -> FALSE]
        /\ number   = [p \in 1..NumProcs -> 0]
        /\ inCS    = [p \in 1..NumProcs -> FALSE]

\* Next-state relation for a single process
NextProc(p) ==
    \/ /\ choosing[p] = FALSE
       /\ number[p] = 0
       /\ \/ \E q \in 1..NumProcs : inCS[q]
          \/ \E q \in 1..NumProcs : choosing[q]
          \/ \E q \in 1..NumProcs : number[q] # 0 /\ (number[q] < number[p] \/ (number[q] = number[p] /\ q < p))
       /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    \/ /\ choosing[p] = FALSE
       /\ number[p] > 0
       /\ \A q \in 1..NumProcs : q # p -> (number[q] = 0 \/ number[q] > number[p] \/ (number[q] = number[p] /\ q < p))
       /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    \/ /\ choosing'[p] = TRUE
       /\ number'[p] = MaxTicket + 1 \* Temporary value to ensure fairness
    \/ /\ choosing[p] = TRUE
       /\ number'[p] = (Max( {number[q] | q \in 1..NumProcs} ) + 1) % (MaxTicket + 1)
       /\ choosing'[p] = FALSE

\* Next-state relation for the system
Next == \E p \in 1..NumProcs : NextProc(p)

\* Specification of the system behavior
Spec ==
    Init /\ [][Next]_<<choosing, number, inCS>>

\* Safety property: mutual exclusion
MutualExclusion == \A p, q \in 1..NumProcs : p # q -> \/ ~inCS[p] \/ ~inCS[q]

\* Liveness property: starvation-freedom (fairness assumption)
StarvationFreedom ==
    WF_<<choosing, number, inCS>>(Next)

\* Boundedness property
Boundedness == \A p \in 1..NumProcs : number[p] \leq MaxTicket

\* Absence of deadlock
NoDeadlock ==
    [](\/ \E p \in 1..NumProcs : choosing[p]
        \/ \E p \in 1..NumProcs : inCS[p]
        \/ \A p \in 1..NumProcs : number[p] = 0)

\* Invariant: combination of safety and boundedness
Invariant ==
    MutualExclusion /\ Boundedness

=============================================================================