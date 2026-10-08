---------------------------- MODULE MutualExclusion ----------------------------

CONSTANTS N \* Number of processes

VARIABLES turn, ticket, in_critical

\* Initialization predicate
Init == /\ turn = 0
        /\ ticket = [p \in 1..N -> 0]
        /\ in_critical = [p \in 1..N -> FALSE]

\* Action for a process to request entry into the critical section
RequestEntry(p) ==
    /\ ticket' = [ticket EXCEPT ![p] = Max(ticket[p], turn) + 1]
    /\ UNCHANGED <<turn, in_critical>>

\* Condition for a process to enter the critical section
CanEnter(p) == 
    \A q \in 1..N: (q # p) => ticket[q] <= ticket[p] \/ ~in_critical[q]

\* Action for a process to enter the critical section
EnterCritical(p) ==
    /\ CanEnter(p)
    /\ in_critical' = [in_critical EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<turn, ticket>>

\* Action for a process to exit the critical section
ExitCritical(p) ==
    /\ in_critical' = [in_critical EXCEPT ![p] = FALSE]
    /\ turn' = Max(ticket[p], turn)
    /\ UNCHANGED ticket

\* Next-state relation
Next == 
    \E p \in 1..N: \/ RequestEntry(p)
                     \/ (in_critical[p] -> ExitCritical(p))
                     \/ (~in_critical[p] /\ CanEnter(p) -> EnterCritical(p))

\* Specification of the system
Spec == Init /\ [][Next]_<<turn, ticket, in_critical>>

\* Safety invariant: mutual exclusion
Invariant ==
    \A p1, p2 \in 1..N: (p1 # p2) => ~in_critical[p1] \/ ~in_critical[p2]

\* Conditional liveness property: if some process is trying to enter the critical section,
\* then eventually some process will enter the critical section
CondLiveness ==
    [](\/ p \in 1..N: in_critical[p]) =>
        <>(\/ p \in 1..N: CanEnter(p) /\ ~in_critical[p])

\* Fairness specification for nonblocking progress points
FairSpec ==
    WF_next(<<turn, ticket, in_critical>>, Next)

=============================================================================