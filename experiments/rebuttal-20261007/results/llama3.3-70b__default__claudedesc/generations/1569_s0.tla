```tla
MODULE CBakery

EXTENDS Integers, FiniteSets

CONSTANTS NumProcs, MaxNum

VARIABLES num, choosing, read, max, nxt, pc

Init ==
  /\ num = [i \in 1..NumProcs |-> 0]
  /\ choosing = [i \in 1..NumProcs |-> FALSE]
  /\ read = [i \in 1..NumProcs |-> {}]
  /\ max = [i \in 1..NumProcs |-> 0]
  /\ nxt = [i \in 1..NumProcs |-> 0]
  /\ pc = [i \in 1..NumProcs |-> "d1"]

Next ==
  \E i \in 1..NumProcs :
    IF pc[i] = "d1" THEN
      /\ choosing' = [choosing EXCEPT ![i] = TRUE]
      /\ read' = [read EXCEPT ![i] = {}]
      /\ max' = [max EXCEPT ![i] = 0]
      /\ nxt' = [nxt EXCEPT ![i] = 0]
      /\ pc' = [pc EXCEPT ![i] = "d2"]
      /\ num' = num
    ELSE IF pc[i] = "d2" THEN
      /\ choosing' = choosing
      /\ read' = [read EXCEPT ![i] = read[i] \cup {num[j] : j \in 1..NumProcs}]
      /\ max' = [max EXCEPT ![i] = IF read'[i] = {} THEN 0 ELSE Max(read'[i])]
      /\ nxt' = [nxt EXCEPT ![i] = max'[i] + 1]
      /\ pc' = [pc EXCEPT ![i] = "d3"]
      /\ num' = num
    ELSE IF pc[i] = "d3" THEN
      /\ choosing' = [choosing EXCEPT ![i] = FALSE]
      /\ read' = read
      /\ max' = max
      /\ nxt' = nxt
      /\ pc' = [pc EXCEPT ![i] = "w1"]
      /\ num' = [num EXCEPT ![i] = nxt[i]]
    ELSE IF pc[i] = "w1" THEN
      /\ choosing' = choosing
      /\ read' = read
      /\ max' = max
      /\ nxt' = nxt
      /\ pc' = [pc EXCEPT ![i] = "w2"]
      /\ num' = num
    ELSE IF pc[i] = "w2" THEN
      /\ choosing' = choosing
      /\ read' = read
      /\ max' = max
      /\ nxt' = nxt
      /\ pc' = [pc EXCEPT ![i] = "cs"]
      /\ num' = num
    ELSE IF pc[i] = "cs" THEN
      /\ choosing' = choosing
      /\ read' = read
      /\ max' = max
      /\ nxt' = nxt
      /\ pc' = [pc EXCEPT ![i] = "d1"]
      /\ num' = [num EXCEPT ![i] = 0]
    ELSE
      /\ choosing' = choosing
      /\ read' = read
      /\ max' = max
      /\ nxt' = nxt
      /\ pc' = pc
      /\ num' = num

Spec ==
  Init /\ [][Next]_vars

THEOREM Spec => []~(EX i, j \in 1..NumProcs : i # j /\ pc[i] = "cs" /\ pc[j] = "cs")

CONSTRAINT StateConstraint == \A i \in 1..NumProcs : num[i] <= MaxNum
```