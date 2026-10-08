```
MODULE BakeryAlgorithm
EXTENDS Integers, Sequences

CONSTANTS NumProcs
VARIABLES tickets, choosing, readSet, maxima, nextExamined, pc

Init ==
  /\ tickets = [i \in 1..NumProcs |-> 0]
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ readSet = [i \in 1..NumProcs |-> {}]
  /\ maxima = [i \in 1..NumProcs |-> 0]
  /\ nextExamined = [i \in 1..NumProcs |-> 1]
  /\ pc = [i \in 1..NumProcs |-> "start"]

Next ==
  \/ \E i \in 1..NumProcs :
    /\ pc[i] = "start"
    /\ tickets[i] = 0
    /\ choosing[i] = TRUE
    /\ readSet[i] = {}
    /\ maxima[i] = 0
    /\ nextExamined[i] = 1
    /\ pc' = [pc EXCEPT ![i] = "trying"]
    /\ tickets' = tickets
    /\ choosing' = choosing
    /\ readSet' = readSet
    /\ maxima' = maxima
    /\ nextExamined' = nextExamined
  \/ \E i \in 1..NumProcs :
    /\ pc[i] = "trying"
    /\ tickets[i] > 0
    /\ choosing[i] = TRUE
    /\ readSet[i] = {}
    /\ maxima[i] = 0
    /\ nextExamined[i] = 1
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ tickets' = tickets
    /\ choosing' = choosing
    /\ readSet' = readSet
    /\ maxima' = maxima
    /\ nextExamined' = nextExamined
  \/ \E i \in 1..NumProcs :
    /\ pc[i] = "critical"
    /\ tickets[i] > 0
    /\ choosing[i] = FALSE
    /\ readSet[i] = {}
    /\ maxima[i] = 0
    /\ nextExamined[i] = NumProcs
    /\ pc' = [pc EXCEPT ![i] = "end"]
    /\ tickets' = tickets
    /\ choosing' = choosing
    /\ readSet' = readSet
    /\ maxima' = maxima
    /\ nextExamined' = nextExamined
  \/ \E i \in 1..NumProcs :
    /\ pc[i] = "end"
    /\ tickets[i] = 0
    /\ choosing[i] = FALSE
    /\ readSet[i] = {}
    /\ maxima[i] = 0
    /\ nextExamined[i] = 1
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ tickets' = tickets
    /\ choosing' = choosing
    /\ readSet' = readSet
    /\ maxima' = maxima
    /\ nextExamined' = nextExamined

Spec ==
  Init /\ [][Next]_tickets /\ [][Next]_choosing /\ [][Next]_readSet /\ [][Next]_maxima /\ [][Next]_nextExamined /\ [][Next]_pc

Inv == 
  /\ \A i, j \in 1..NumProcs : pc[i] = "critical" \/ pc[j] = "critical" => i = j
  /\ \A i \in 1..NumProcs : tickets[i] <= NumProcs

THEOREM Spec => []Inv
```