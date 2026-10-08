---------------------------- MODULE Bakery --------------------------------
EXTENDS Integers, FiniteSets

CONSTANT NumProcs, MaxNum

VARIABLES tickets, choosing, inCS

Init ==
  /\ tickets = [i \in 1..NumProcs |-> 0]
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ inCS = [i \in 1..NumProcs |-> FALSE]

Next ==
  \/ \E i \in 1..NumProcs :
      /\ ~inCS[i]
      /\ choosing' = [choosing EXCEPT ![i] = TRUE]
      /\ tickets' = tickets
      /\ inCS' = inCS
  \/ \E i \in 1..NumProcs :
      /\ choosing[i]
      /\ tickets' = [tickets EXCEPT ![i] = 1 + Max([j \in 1..NumProcs |-> IF choosing[j] THEN -1 ELSE tickets[j]])]
      /\ choosing' = [choosing EXCEPT ![i] = FALSE]
      /\ inCS' = inCS
  \/ \E i \in 1..NumProcs :
      /\ ~choosing[i]
      /\ ~inCS[i]
      /\ \A j \in 1..NumProcs : ~(tickets[j] < tickets[i]) \/ (tickets[j] = tickets[i] /\ j >= i)
      /\ inCS' = [inCS EXCEPT ![i] = TRUE]
      /\ choosing' = choosing
      /\ tickets' = tickets
  \/ \E i \in 1..NumProcs :
      /\ inCS[i]
      /\ inCS' = [inCS EXCEPT ![i] = FALSE]
      /\ choosing' = choosing
      /\ tickets' = [tickets EXCEPT ![i] = 0]

Spec == Init /\ [][Next]_<<tickets, choosing, inCS>>

Invariant ==
  /\ \A i \in 1..NumProcs : tickets[i] >= 0
  /\ \A i \in 1..NumProcs : tickets[i] <= MaxNum
  /\ \A i, j \in 1..NumProcs : ~(inCS[i] /\ inCS[j]) \/ i = j

THEOREM Spec => []Invariant
=============================================================================