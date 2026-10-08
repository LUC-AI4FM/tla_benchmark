```
MODULE Bakery
EXTENDS Integers, FiniteSets

CONSTANTS NumProcs, MaxTicket
VARIABLES choosing, num, inCS

Init ==
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ num = [i \in 1..NumProcs |-> 0]
  /\ inCS = [i \in 1..NumProcs |-> FALSE]

Next ==
  \/ \E i \in 1..NumProcs :
    /\ ~inCS[i]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ num' = num
    /\ inCS' = inCS
  \/ \E i \in 1..NumProcs :
    /\ choosing[i]
    /\ choosing' = choosing
    /\ num' = [num EXCEPT ![i] = 1 + Max({num[j] : j \in 1..NumProcs})]
    /\ inCS' = inCS
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  \/ \E i \in 1..NumProcs :
    /\ ~choosing[i]
    /\ num[i] # 0
    /\ \A j \in 1..NumProcs : j # i => (choosing[j] => num[j] > num[i]) \/ (num[j] = num[i] => j > i)
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ choosing' = choosing
    /\ num' = num
  \/ \E i \in 1..NumProcs :
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ choosing' = choosing
    /\ num' = num

Spec == Init /\ [][Next]_choosing, num, inCS

THEOREM Spec => []\A i, j \in 1..NumProcs : i # j => ~(inCS[i] /\ inCS[j])
```