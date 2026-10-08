------------------------------- MODULE BakeryAlgorithm -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxTicket
ASSUME N \in Nat /\ N > 0
ASSUME MaxTicket \in Nat /\ MaxTicket > 0

VARIABLES choosing, ticket, inCS

Init == 
    /\ choosing = [t \in 1..N -> FALSE]
    /\ ticket   = [t \in 1..N -> 0]
    /\ inCS    = [t \in 1..N -> FALSE]

Next ==
    \/ \E t \in 1..N : 
        (choosing[t] = FALSE
         /\ ticket[t] = 0
         /\ inCS[t] = FALSE
         /\ choosing' = [choosing EXCEPT ![t] = TRUE]
         /\ ticket'   = [ticket EXCEPT ![t] = Max( {ticket[s] : s \in 1..N} ) + 1 ]
         /\ inCS'    = inCS)
    \/ \E t \in 1..N :
        (choosing[t] = TRUE
         /\ ticket[t] > 0
         /\ inCS[t] = FALSE
         /\ choosing' = [choosing EXCEPT ![t] = FALSE]
         /\ ticket'   = ticket
         /\ inCS'    = inCS)
    \/ \E t \in 1..N :
        (choosing[t] = FALSE
         /\ ticket[t] > 0
         /\ inCS[t] = FALSE
         /\ \A s \in 1..N : 
            (s = t \/ choosing[s] = FALSE \/ ticket[s] = 0 \/ ticket[s] > ticket[t] \/ (ticket[s] = ticket[t] /\ s > t))
         /\ choosing' = choosing
         /\ ticket'   = ticket
         /\ inCS'    = [inCS EXCEPT ![t] = TRUE])
    \/ \E t \in 1..N :
        (choosing[t] = FALSE
         /\ ticket[t] > 0
         /\ inCS[t] = TRUE
         /\ choosing' = choosing
         /\ ticket'   = [ticket EXCEPT ![t] = 0]
         /\ inCS'    = [inCS EXCEPT ![t] = FALSE])

Spec ==
    /\ Init
    /\ [][Next]_<<choosing, ticket, inCS>>
    /\ WF_next(<<choosing, ticket, inCS>>)

(* Safety: Mutual Exclusion *)
MutualExclusion == \A t1, t2 \in 1..N : t1 # t2 => ~ (inCS[t1] /\ inCS[t2])

(* Liveness: Starvation Freedom *)
StarvationFreedom ==
    \A t \in 1..N :
        <>[](\E s \in 1..N : choosing[s] \/ ticket[s] > 0) 
        -> <>(\E s \in 1..N : inCS[s])

(* Boundedness: Ticket Values *)
BoundedTickets == \A t \in 1..N : ticket[t] \leq MaxTicket

(* Absence of Deadlock *)
NoDeadlock ==
    ~(\E t \in 1..N :
        choosing[t] = FALSE
        /\ ticket[t] > 0
        /\ inCS[t] = FALSE
        /\ (\A s \in 1..N : (s = t \/ choosing[s] = TRUE \/ (ticket[s] > 0 /\ (ticket[s] < ticket[t] \/ (ticket[s] = ticket[t] /\ s < t)))))

=============================================================================