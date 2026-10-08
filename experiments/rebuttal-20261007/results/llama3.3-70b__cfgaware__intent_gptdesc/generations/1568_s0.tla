--------------------------- MODULE BakeryAlgorithm ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT NumProcs, MaxTicket
VARIABLE choosing, tickets, inCS, maxObserved

Spec == 
  /\ choosing \in [1..NumProcs -> {TRUE, FALSE}]
  /\ tickets \in [1..NumProcs -> 0..MaxTicket]
  /\ inCS \in [1..NumProcs -> {TRUE, FALSE}]
  /\ maxObserved \in [1..NumProcs -> 0..MaxTicket]
  /\ Init
  /\ [][Next]_choosing /\
      [][Next]_tickets /\
      [][Next]_inCS /\
      [][Next]_maxObserved

Init == 
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ tickets = [i \in 1..NumProcs |-> 0]
  /\ inCS = [i \in 1..NumProcs |-> FALSE]
  /\ maxObserved = [i \in 1..NumProcs |-> 0]

Next == 
  \/ \E i \in 1..NumProcs :
      /\ ~choosing[i]
      /\ choosing' = [choosing EXCEPT ![i] = TRUE]
      /\ tickets' = tickets
      /\ inCS' = inCS
      /\ maxObserved' = maxObserved
  \/ \E i \in 1..NumProcs :
      /\ choosing[i]
      /\ ~inCS[i]
      /\ maxObserved' = [maxObserved EXCEPT ![i] = MaxTicket]
      /\ tickets' = [tickets EXCEPT ![i] = maxObserved'[i] + 1]
      /\ choosing' = [choosing EXCEPT ![i] = FALSE]
      /\ inCS' = inCS
      /\ maxObserved = [maxObserved EXCEPT ![i] = MaxTicket]
  \/ \E i \in 1..NumProcs :
      /\ ~choosing[i]
      /\ ~inCS[i]
      /\ tickets[i] # 0
      /\ \A j \in 1..NumProcs : 
          ~(tickets[j] # 0 /\ (tickets[j] < tickets[i] \/ (tickets[j] = tickets[i] /\ j < i)))
      /\ inCS' = [inCS EXCEPT ![i] = TRUE]
      /\ choosing' = choosing
      /\ tickets' = tickets
      /\ maxObserved' = maxObserved
  \/ \E i \in 1..NumProcs :
      /\ inCS[i]
      /\ inCS' = [inCS EXCEPT ![i] = FALSE]
      /\ choosing' = choosing
      /\ tickets' = [tickets EXCEPT ![i] = 0]
      /\ maxObserved' = maxObserved

Invariant == 
  /\ \A i, j \in 1..NumProcs : i # j => ~(inCS[i] /\ inCS[j])
  /\ \A i \in 1..NumProcs : tickets[i] <= MaxTicket
  /\ \A i \in 1..NumProcs : choosing[i] \/ inCS[i] => tickets[i] # 0

THEOREM Spec => []Invariant
=============================================================================