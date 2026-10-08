------------------------------- MODULE BakeryAlgorithm -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxTicket

VARIABLES ticket, choosing, inCS

Init == /\ ticket \in [1..N -> 0]
        /\ choosing \in [1..N -> FALSE]
        /\ inCS \in [1..N -> FALSE]

Next ==
    \/ \E i \in 1..N : 
        (/\ ~choosing[i] 
         /\ ~inCS[i]
         /\ ticket[i] = 0
         /\ choosing' = [choosing EXCEPT ![i] = TRUE]
         /\ ticket' = [ticket EXCEPT ![i] = 1 + Max({ticket[j] | j \in 1..N})]
         /\ inCS' = inCS)
    \/ \E i \in 1..N : 
        (/\ choosing[i]
         /\ ~inCS[i]
         /\ ticket[i] > 0
         /\ (\A j \in 1..N \ {i} : 
                (ticket[j] = 0) \/ 
                (ticket[j] > ticket[i]) \/ 
                (ticket[j] = ticket[i] /\ j < i))
         /\ choosing' = [choosing EXCEPT ![i] = FALSE]
         /\ inCS' = [inCS EXCEPT ![i] = TRUE])
    \/ \E i \in 1..N : 
        (/\ inCS[i]
         /\ inCS' = [inCS EXCEPT ![i] = FALSE]
         /\ ticket' = [ticket EXCEPT ![i] = 0])

Spec == Init /\ [][Next]_<<choosing, ticket, inCS>>

MutualExclusion == \A i, j \in 1..N : i # j => ~inCS[i] \/ ~inCS[j]

SafetyOfTicketManagement ==
    /\ \A i \in 1..N : ticket[i] \leq MaxTicket
    /\ \A i \in 1..N : inCS[i] => ticket[i] = 0

Liveness == 
    WF_<<choosing>>_<<Next>>
    /\ SF_<<choosing>>_<<Next>>

AbsenceOfDeadlock ==
    [](\/ \E i \in 1..N : ~inCS[i] => choosing[i]
        \/ \E i \in 1..N : inCS[i])

TypeOK ==
    /\ ticket \in [1..N -> 0..MaxTicket]
    /\ choosing \in [1..N -> BOOLEAN]
    /\ inCS \in [1..N -> BOOLEAN]

Inv == TypeOK /\ MutualExclusion /\ SafetyOfTicketManagement

THEOREM Spec => []Inv
THEOREM Spec => Liveness
THEOREM Spec => AbsenceOfDeadlock
=============================================================================