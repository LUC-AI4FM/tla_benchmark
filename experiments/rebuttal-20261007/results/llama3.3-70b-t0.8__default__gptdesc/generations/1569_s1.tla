```
MODULE Bakery
EXTENDS Integers, FiniteSets

CONSTANTS NumProcs
VARIABLES tickets, choosing, readSet, maxVal, nextExamined, pc

Init ==
  /\ tickets = [i \in 1..NumProcs |-> 0]
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ readSet = [i \in 1..NumProcs |-> {}]
  /\ maxVal = 0
  /\ nextExamined = 1
  /\ pc = [i \in 1..NumProcs |-> "NCS"]

Next ==
  \/ \E i \in 1..NumProcs :
      /\ pc[i] = "NCS"
      /\ choosing[i] = FALSE
      /\ tickets[i] = 0
      /\ pc' = [pc EXCEPT ![i] = "TRY"]
      /\ tickets' = tickets
      /\ choosing' = [choosing EXCEPT ![i] = TRUE]
      /\ readSet' = readSet
      /\ maxVal' = maxVal
      /\ nextExamined' = nextExamined
  \/ \E i \in 1..NumProcs :
      /\ pc[i] = "TRY"
      /\ choosing[i] = TRUE
      /\ tickets[i] = 0
      /\ tickets' = [tickets EXCEPT ![i] = maxVal + 1]
      /\ choosing' = [choosing EXCEPT ![i] = FALSE]
      /\ readSet' = [readSet EXCEPT ![i] = 1..NumProcs]
      /\ maxVal' = maxVal + 1
      /\ nextExamined' = 1
      /\ pc' = [pc EXCEPT ![i] = "WAIT"]
      \/ \E i \in 1..NumProcs :
          /\ pc[i] = "WAIT"
          /\ \A j \in readSet[i] : tickets[j] = 0 \/ tickets[j] > tickets[i]
          /\ pc' = [pc EXCEPT ![i] = "CS"]
          /\ tickets' = tickets
          /\ choosing' = choosing
          /\ readSet' = readSet
          /\ maxVal' = maxVal
          /\ nextExamined' = nextExamined
  \/ \E i \in 1..NumProcs :
      /\ pc[i] = "CS"
      /\ pc' = [pc EXCEPT ![i] = "NCS"]
      /\ tickets' = tickets
      /\ choosing' = choosing
      /\ readSet' = readSet
      /\ maxVal' = maxVal
      /\ nextExamined' = nextExamined

Spec == Init /\ [][Next]_<<tickets, choosing, readSet, maxVal, nextExamined, pc>>
           /\ WF_<<tickets, choosing, readSet, maxVal, nextExamined, pc>>(Next)

Inv == \A i, j \in 1..NumProcs : 
       pc[i] = "CS" /\ pc[j] = "CS" => i = j

BoundedTickets == \A i \in 1..NumProcs : tickets[i] <= NumProcs
```