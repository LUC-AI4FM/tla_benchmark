```tla
                         ![n] = [k \in Keys |-> IF k \in KL THEN childOf[n][k] ELSE NIL],
                         ![m] = [k \in Keys |-> IF k \in KR THEN childOf[n][k] ELSE NIL],
                         ![p] = [k \in Keys |->
                                   IF k = piv THEN n
                                   ELSE IF k = k0 THEN m
                                   ELSE childOf[p][k]]]
          /\ lastOf' = [lastOf EXCEPT
                         ![n] = childOf[n][piv],
                         ![m] = lastOf[n],
                         ![p] = IF isLast THEN m ELSE lastOf[p]]
          /\ inUse' = inUse \cup {m}
          /\ root' = root
          /\ UNCHANGED valOf
          /\ AfterSplit(root)

SplitRootLeaf ==
    /\ state = SPLIT_ROOT_LEAF
    /\ LET n == focus
           m == Min(FreeNodes)
           r == Min(FreeNodes \ {m})
           L == LowerHalf(keysOf[n])
           U == keysOf[n] \ L
           s == Min(U)
       IN /\ isLeaf' = [isLeaf EXCEPT ![m] = TRUE, ![r] = FALSE]
          /\ keysOf' = [keysOf EXCEPT ![n] = L, ![m] = U, ![r] = {s}]
          /\ valOf' = [valOf EXCEPT
                         ![n] = [k \in Keys |-> IF k \in L THEN valOf[n][k] ELSE NIL],
                         ![m] = [k \in Keys |-> IF k \in U THEN valOf[n][k] ELSE NIL]]
          /\ childOf' = [childOf EXCEPT
                         ![r] = [k \in Keys |-> IF k = s THEN n ELSE NIL]]
          /\ lastOf' = [lastOf EXCEPT ![r] = m]
          /\ inUse' = inUse \cup {m, r}
          /\ root' = r
          /\ AfterSplit(r)

SplitRootInner ==
    /\ state = SPLIT_ROOT_INNER
    /\ LET n == focus
           m == Min(FreeNodes)
           r == Min(FreeNodes \ {m})
           K == keysOf[n]
           piv == Pivot(K)
           KL == {x \in K : x < piv}
           KR == {x \in K : x > piv}
       IN /\ isLeaf' = [isLeaf EXCEPT ![m] = FALSE, ![r] = FALSE]
          /\ keysOf' = [keysOf EXCEPT ![n] = KL, ![m] = KR, ![r] = {piv}]
          /\ childOf' = [childOf EXCEPT
                         ![n] = [k \in Keys |-> IF k \in KL THEN childOf[n][k] ELSE NIL],
                         ![m] = [k \in Keys |-> IF k \in KR THEN childOf[n][k] ELSE NIL],
                         ![r] = [k \in Keys |-> IF k = piv THEN n ELSE NIL]]
          /\ lastOf' = [lastOf EXCEPT
                         ![n] = childOf[n][piv],
                         ![m] = lastOf[n],
                         ![r] = m]
          /\ inUse' = inUse \cup {m, r}
          /\ root' = r
          /\ UNCHANGED valOf
          /\ AfterSplit(r)

-----------------------------------------------------------------------------

Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ GetValue
    \/ UpdateLeaf
    \/ FindLeafToAdd
    \/ WhichToSplit
    \/ AddToLeaf
    \/ SplitLeaf
    \/ SplitInner
    \/ SplitRootLeaf
    \/ SplitRootInner

Spec == Init /\ [][Next]_vars

\* Abstract key-value store view: when READY, Mapping is the dictionary
AbstractDict == IF state = READY THEN Mapping ELSE Mapping

=============================================================================
```