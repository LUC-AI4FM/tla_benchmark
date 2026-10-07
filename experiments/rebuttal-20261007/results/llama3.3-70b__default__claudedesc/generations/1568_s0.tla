```tla
MODULE BakeryAlgorithm

EXTENDS Integers

CONSTANTS NumProcs, MaxNum

VARIABLES num, choosing, read, max, nxt, pc

Init ==
  /\ num = [i \in Proc |-> 0]
  /\ choosing = [i \in Proc |-> FALSE]
  /\ read = [i \in Proc |-> 0]
  /\ max = [i \in Proc |-> 0]
  /\ nxt = [i \in Proc |-> 0]
  /\ pc = [i \in Proc |-> "loop"]

Next ==
  \/ \E i \in Proc :
      IF pc[i] = "loop" THEN
        /\ choosing' = [choosing EXCEPT ![i] = TRUE]
        /\ pc' = [pc EXCEPT ![i] = "d1"]
        /\ UNCHANGED <<num, read, max, nxt>>
      ELSE IF pc[i] = "d1" THEN
        /\ read' = [read EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT ![i] = "d2"]
        /\ UNCHANGED <<num, choosing, max, nxt>>
      ELSE IF pc[i] = "d2" THEN
        /\ read' = [read EXCEPT ![i] = read[i] + 1]
        /\ IF read'[i] > NumProcs THEN
            /\ num' = [num EXCEPT ![i] = max[i] + 1]
            /\ choosing' = [choosing EXCEPT ![i] = FALSE]
            /\ pc' = [pc EXCEPT ![i] = "w1"]
          ELSE
            /\ max' = [max EXCEPT ![i] = IF read'[i] \in Proc /\ (num[read'[i]] > max[i]) THEN num[read'[i]] ELSE max[i]]
            /\ UNCHANGED <<num, choosing, pc>>
        /\ UNCHANGED nxt
      ELSE IF pc[i] = "d3" THEN
        /\ UNCHANGED num
        /\ UNCHANGED choosing
        /\ UNCHANGED read
        /\ UNCHANGED max
        /\ UNCHANGED nxt
        /\ pc' = [pc EXCEPT ![i] = "w1"]
      ELSE IF pc[i] = "w1" THEN
        /\ nxt' = [nxt EXCEPT ![i] = 1]
        /\ pc' = [pc EXCEPT ![i] = "w2"]
        /\ UNCHANGED <<num, choosing, read, max>>
      ELSE IF pc[i] = "w2" THEN
        /\ IF nxt[i] > NumProcs THEN
            /\ pc' = [pc EXCEPT ![i] = "cs"]
          ELSE
            /\ IF choosing[nxt[i]] THEN
                /\ UNCHANGED pc
              ELSE
                /\ IF num[nxt[i]] = 0 \/ (num[nxt[i]] > num[i]) \/ (num[nxt[i]] = num[i] /\ nxt[i] > i) THEN
                    /\ nxt' = [nxt EXCEPT ![i] = nxt[i] + 1]
                    /\ pc' = [pc EXCEPT ![i] = "w2"]
                  ELSE
                    /\ UNCHANGED pc
        /\ UNCHANGED <<num, choosing, read, max>>
      ELSE IF pc[i] = "cs" THEN
        /\ num' = [num EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT ![i] = "loop"]
        /\ UNCHANGED <<choosing, read, max, nxt>>
  \/ \E i \in Proc :
      /\ pc[i] = "cs"
      /\ num' = num
      /\ choosing' = choosing
      /\ read' = read
      /\ max' = max
      /\ nxt' = nxt
      /\ pc' = [pc EXCEPT ![i] = "cs"]

Invariant ==
  /\ \A i, j \in Proc : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")
  /\ \A i \in Proc : num[i] <= MaxNum

Spec == Init /\ [][Next]_<<num, choosing, read, max, nxt, pc>>

THEOREM Spec => []Invariant
```