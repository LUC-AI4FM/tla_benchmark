```
MODULE Bakery
EXTENDS Integers, FiniteSets

CONSTANTS NumProcs, MaxTicket
VARIABLES choosing, tickets, inCS, pc

Init ==
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ tickets = [i \in 1..NumProcs |-> 0]
  /\ inCS = [i \in 1..NumProcs |-> FALSE]
  /\ pc = [i \in 1..NumProcs |-> "start"]

Next ==
  \/ \E i \in 1..NumProcs :
    /\ pc[i] = "start"
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ tickets' = tickets
    /\ inCS' = inCS
    /\ pc' = [pc EXCEPT ![i] = "read"]
  \/ \E i \in 1..NumProcs :
    /\ pc[i] = "read"
    /\ choosing[i]
    /\ \E max \in Nat :
      /\ max = Max({tickets[j] : j \in 1..NumProcs /\ ~choosing[j]})
      /\ tickets' = [tickets EXCEPT ![i] = max + 1]
      /\ choosing' = [choosing EXCEPT ![i] = FALSE]
      /\ inCS' = inCS
      /\ pc' = [pc EXCEPT ![i] = "wait"]
  \/ \E i \in 1..NumProcs :
    /\ pc[i] = "wait"
    /\ ~inCS[i]
    /\ \A j \in 1..NumProcs :
      (j = i) \/ (tickets[j] = 0) \/ (tickets[j] > tickets[i]) \/ (tickets[j] = tickets[i] /\ j > i)
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ choosing' = choosing
    /\ tickets' = tickets
    /\ pc' = [pc EXCEPT ![i] = "cs"]
  \/ \E i \in 1..NumProcs :
    /\ pc[i] = "cs"
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ tickets' = [tickets EXCEPT ![i] = 0]
    /\ choosing' = choosing
    /\ pc' = [pc EXCEPT ![i] = "start"]

Spec ==
  /\ Init
  /\ [][Next]_choosing, tickets, inCS, pc
  /\ WF_vars(Next, choosing, tickets, inCS, pc)

THEOREM Spec => []~(\E i, j \in 1..NumProcs : i # j /\ inCS[i] /\ inCS[j])

INVARIANT tickets \in [1..NumProcs -> 0..MaxTicket]
```
Note: The `WF_vars` operator is used to specify weak fairness for the variables. This ensures that every process will eventually make progress if it is continuously enabled.