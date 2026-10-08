```
MODULE BakeryAlgorithm
EXTENDS Integers, Sequences

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
  /\ \E i \in 1..NumProcs :
    /\ (pc[i] = "NCS") 
      /\ (tickets[i] = 0)
      /\ choosing[i] = TRUE
      /\ pc' = [pc EXCEPT ![i] = "TRY"]
    /\ tickets' = tickets
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ readSet' = readSet
    /\ max' = max
    /\ nextExamined' = nextExamined
  \/ \E i \in 1..NumProcs :
    /\ (pc[i] = "TRY")
      /\ (tickets[i] > 0)
      /\ choosing[i] = TRUE
      /\ readSet[i] = {}
      /\ pc' = [pc EXCEPT ![i] = "REM"]
      /\ tickets' = [tickets EXCEPT ![i] = tickets[i] + 1]
      /\ choosing' = choosing
      /\ readSet' = [readSet EXCEPT ![i] = {j \in 1..NumProcs : tickets[j] < tickets[i]}]
      /\ max' = IF tickets[i] > max THEN tickets[i] ELSE max
      /\ nextExamined' = nextExamined
  \/ \E i \in 1..NumProcs :
    /\ (pc[i] = "REM")
      /\ choosing[i] = TRUE
      /\ readSet[i] # {}
      /\ pc' = [pc EXCEPT ![i] = "WAIT"]
      /\ tickets' = tickets
      /\ choosing' = choosing
      /\ readSet' = [readSet EXCEPT ![i] = {}]
      /\ max' = max
      /\ nextExamined' = IF nextExamined = NumProcs THEN 1 ELSE nextExamined + 1
  \/ \E i \in 1..NumProcs :
    /\ (pc[i] = "WAIT")
      /\ choosing[i] = TRUE
      /\ readSet[i] = {}
      /\ pc' = [pc EXCEPT ![i] = "CS"]
      /\ tickets' = tickets
      /\ choosing' = [choosing EXCEPT ![i] = FALSE]
      /\ readSet' = readSet
      /\ max' = max
      /\ nextExamined' = nextExamined
  \/ \E i \in 1..NumProcs :
    /\ (pc[i] = "CS")
      /\ choosing[i] = FALSE
      /\ pc' = [pc EXCEPT ![i] = "NCS"]
      /\ tickets' = [tickets EXCEPT ![i] = 0]
      /\ choosing' = choosing
      /\ readSet' = readSet
      /\ max' = IF max = tickets[i] THEN 0 ELSE max
      /\ nextExamined' = nextExamined

Spec == Init /\ [][Next]_

TypeInvariant == 
  /\ pc \in [1..NumProcs -> {"NCS", "TRY", "REM", "WAIT", "CS"}]
  /\ tickets \in [1..NumProcs -> Nat]
  /\ choosing \in [1..NumProcs -> Bool]
  /\ readSet \in [1..NumProcs -> SUBSET 1..NumProcs]
  /\ max \in Nat
  /\ nextExamined \in 1..NumProcs

MutualExclusion == <<pc>>_11 = 1

THEOREM Spec => []TypeInvariant
THEOREM Spec => []MutualExclusion

FAIRNESS pc
```
Note that the fairness condition in TLA+ requires additional constraints (e.g., WF or SF) which are not specified here. For TLC model checking, you would typically use a bounded model with specific values for constants like `NumProcs`.