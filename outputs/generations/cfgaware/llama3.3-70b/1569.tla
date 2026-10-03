```
---------------------------- MODULE Bakery --------------------------------
EXTENDS Integers, FiniteSets

CONSTANT NumProcs
VARIABLES tickets, choosing, readSet, max, nextExamined, pc

Spec == 
  /\ tickets = [i \in 1..NumProcs |-> 0]
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ readSet = [i \in 1..NumProcs |-> {}]
  /\ max = 0
  /\ nextExamined = 1
  /\ pc = [i \in 1..NumProcs |-> "start"]
  /\ [][
      \/ \E i \in 1..NumProcs :
          /\ pc[i] = "start"
          /\ pc' = [pc EXCEPT ![i] = "loop1"]
          /\ tickets' = tickets
          /\ choosing' = choosing
          /\ readSet' = readSet
          /\ max' = max
          /\ nextExamined' = nextExamined
      \/ \E i \in 1..NumProcs :
          /\ pc[i] = "loop1"
          /\ choosing'[i] = TRUE
          /\ tickets'[i] = max + 1
          /\ readSet'[i] = {}
          /\ max' = IF max < tickets'[i] THEN tickets'[i] ELSE max
          /\ nextExamined' = nextExamined
          /\ pc' = [pc EXCEPT ![i] = "loop2"]
          /\ choosing' = [choosing EXCEPT ![i] = TRUE]
          /\ tickets' = [tickets EXCEPT ![i] = tickets'[i]]
          /\ readSet' = [readSet EXCEPT ![i] = readSet'[i]]
      \/ \E i \in 1..NumProcs :
          /\ pc[i] = "loop2"
          /\ nextExamined' = (nextExamined + 1) % NumProcs
          /\ IF nextExamined' = 0 THEN nextExamined' = 1
          /\ readSet'[i] = readSet[i] \cup {nextExamined'}
          /\ max' = IF max < tickets[nextExamined'] THEN tickets[nextExamined'] ELSE max
          /\ pc' = [pc EXCEPT ![i] = "loop3"]
          /\ choosing' = choosing
          /\ tickets' = tickets
          /\ readSet' = [readSet EXCEPT ![i] = readSet'[i]]
          /\ nextExamined' = nextExamined'
      \/ \E i \in 1..NumProcs :
          /\ pc[i] = "loop3"
          /\ choosing'[i] = FALSE
          /\ pc' = [pc EXCEPT ![i] = "critical"]
          /\ choosing' = [choosing EXCEPT ![i] = FALSE]
          /\ tickets' = tickets
          /\ readSet' = readSet
          /\ max' = max
          /\ nextExamined' = nextExamined
      \/ \E i \in 1..NumProcs :
          /\ pc[i] = "critical"
          /\ pc' = [pc EXCEPT ![i] = "end"]
          /\ tickets' = tickets
          /\ choosing' = choosing
          /\ readSet' = readSet
          /\ max' = max
          /\ nextExamined' = nextExamined
      ]

Invariant == 
  \A i, j \in 1..NumProcs : 
    pc[i] = "critical" /\ pc[j] = "critical" => i = j

MaxNum == NumProcs * 2
```
Note: The `Spec` is the main specification of the system. It describes how the variables change over time using a temporal formula (`[]`). Each line within the `Spec` represents an action that can occur in the system, and these actions are combined with disjunctions (`\/`) to represent all possible behaviors.

The `Invariant` property checks for mutual exclusion by ensuring that at most one process is in its critical section at any time. 

Finally, `MaxNum` provides a bound on ticket values for TLC model checking purposes.