------------------------------- MODULE MutualExclusion -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES turn, ticket, in_critical

Init == 
    /\ turn = 0
    /\ ticket = [p \in 1..N -> 0]
    /\ in_critical = [p \in 1..N -> FALSE]

Next ==
    \/ \E p \in 1..N : 
        \* Noncritical section to request critical section
        /\ ~in_critical[p]
        /\ ticket' = [ticket EXCEPT ![p] = Max({ticket[q] : q \in 1..N}) + 1]
        /\ turn' = p
        /\ in_critical' = in_critical
    \/ \E p \in 1..N :
        \* Wait for turn to enter critical section
        /\ ~in_critical[p]
        /\ ticket[p] > 0
        /\ \A q \in 1..N : 
            (q # p => ticket[q] = 0 \/ ticket[q] > ticket[p] \/ (ticket[q] = ticket[p] /\ turn >= q))
        /\ in_critical' = [in_critical EXCEPT ![p] = TRUE]
        /\ turn' = turn
        /\ ticket' = ticket
    \/ \E p \in 1..N :
        \* Exit critical section
        /\ in_critical[p]
        /\ in_critical' = [in_critical EXCEPT ![p] = FALSE]
        /\ ticket' = [ticket EXCEPT ![p] = 0]
        /\ turn' = turn

Spec ==
    WF_next(Next) /\
    Init /\ [][Next]_<<p \in 1..N>> /\
    [](\/ p \in 1..N : in_critical[p] => (\/ q \in 1..N : in_critical[q])) /\
    [](\/ p \in 1..N : ~in_critical[p] /\ ticket[p] > 0 => WF_next(Next))

MutualExclusion == Spec
=============================================================================