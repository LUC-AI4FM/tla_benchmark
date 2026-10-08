```
MODULE BakeryAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N, MaxTicket
VARIABLES choosing, ticket, inCS, read

Init ==
  /\ choosing = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ read = [i \in 1..N |-> {}]

Next ==
  \/ \E i \in 1..N :
    /\ ~choosing[i]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ ticket' = ticket
    /\ inCS' = inCS
    /\ read' = read
  \/ \E i \in 1..N :
    /\ choosing[i]
    /\ ticket' = [ticket EXCEPT ![i] = CHOOSE {t \in 1..MaxTicket : t > (DOMAIN ticket \cup DOMAIN read)[i]}]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ inCS' = inCS
    /\ read' = [read EXCEPT ![i] = DOMAIN ticket]
  \/ \E i \in 1..N :
    /\ ~inCS[i]
    /\ \A j \in 1..N : ~(ticket[j] < ticket[i]) /\ ~(ticket[j] = ticket[i] /\ j < i)
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ choosing' = choosing
    /\ ticket' = ticket
    /\ read' = read
  \/ \E i \in 1..N :
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ choosing' = choosing
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ read' = [read EXCEPT ![i] = {}]

Spec ==
  Init /\ [][Next]_choosing /\ [][Next]_ticket /\ [][Next]_inCS /\ [][Next]_read

MutualExclusion ==
  \A i, j \in 1..N : ~inCS[i] \/ ~inCS[j] \/ i = j

Liveness ==
  WF_vars(choosing, ticket, inCS, read)

SafetyTicketManagement ==
  /\ \A i \in 1..N : ticket[i] \in 0..MaxTicket
  /\ \A i \in 1..N : ~inCS[i] => ticket[i] = 0

AbsenceOfDeadlock ==
  \E i \in 1..N : choosing[i] \/ inCS[i]

TypeInvariant ==
  /\ choosing \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxTicket]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ read \in [1..N -> SUBSET 1..N]

THEOREM Spec => []MutualExclusion
THEOREM Spec => Liveness
THEOREM Spec => []SafetyTicketManagement
THEOREM Spec => []AbsenceOfDeadlock
THEOREM Spec => []TypeInvariant
```