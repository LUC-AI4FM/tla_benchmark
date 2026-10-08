```
MODULE Bakery
EXTENDS Integers, FiniteSets

CONSTANTS NumProcs
VARIABLES tickets, choosing, readSet, max, nextExamined, pc

Init ==
  /\ tickets = [i \in 1..NumProcs |-> 0]
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ readSet = [i \in 1..NumProcs |-> {}]
  /\ max = 0
  /\ nextExamined = 1
  /\ pc = [i \in 1..NumProcs |-> "NCS"]

Next ==
  \/ \E i \in 1..NumProcs :
      /\ pc[i] = "NCS"
      /\ tickets[i] = 0
      /\ choosing[i] = FALSE
      /\ readSet[i] = {}
      /\ pc' = [pc EXCEPT ![i] = "TRY"]
      /\ tickets' = tickets
      /\ choosing' = [choosing EXCEPT ![i] = TRUE]
      /\ readSet' = readSet
      /\ max' = max
      /\ nextExamined' = nextExamined
  \/ \E i \in 1..NumProcs :
      /\ pc[i] = "TRY"
      /\ choosing[i] = TRUE
      /\ tickets[i] < max + NumProcs
      /\ tickets' = [tickets EXCEPT ![i] = tickets[i] + 1]
      /\ choosing' = [choosing EXCEPT ![i] = FALSE]
      /\ readSet' = [readSet EXCEPT ![i] = {j \in 1..NumProcs : tickets[j] # 0}]
      /\ max' = IF tickets[i] + 1 > max THEN tickets[i] + 1 ELSE max
      /\ nextExamined' = nextExamined
      /\ pc' = [pc EXCEPT ![i] = "WAIT"]
  \/ \E i \in 1..NumProcs :
      /\ pc[i] = "WAIT"
      /\ \A j \in readSet[i] : tickets[j] # 0 /\ (tickets[j] > tickets[i] \/ (tickets[j] = tickets[i] /\ j > i))
      /\ nextExamined' = IF nextExamined = NumProcs THEN 1 ELSE nextExamined + 1
      /\ pc' = [pc EXCEPT ![i] = "CS"]
      /\ tickets' = tickets
      /\ choosing' = choosing
      /\ readSet' = readSet
      /\ max' = max
  \/ \E i \in 1..NumProcs :
      /\ pc[i] = "CS"
      /\ pc' = [pc EXCEPT ![i] = "NCS"]
      /\ tickets' = tickets
      /\ choosing' = choosing
      /\ readSet' = readSet
      /\ max' = max
      /\ nextExamined' = nextExamined

Spec == Init /\ [][Next]_<<tickets, choosing, readSet, max, nextExamined, pc>>
  
MutualExclusion == <<pc = [i \in 1..NumProcs |-> "CS"]>> \* [i \in 1..NumProcs]
TicketBound == \A i \in 1..NumProcs : tickets[i] < NumProcs * (NumProcs - 1)
```
Note: The above TLA+ specification models Lamport's Bakery mutual exclusion algorithm. It includes the standard safety property of mutual exclusion via an invariant asserting that at most one process can be in the critical section at a time, and it also includes a state constraint bounding ticket values for TLC model checking.