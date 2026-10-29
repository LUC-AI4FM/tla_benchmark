```tla
EAF_TO_ADD
    /\ UNCHANGED <<op, argKey, argVal, ret, expected, focus, parent,
                   path, dict>>

SplitRootInner ==
    /\ state = SPLIT_ROOT_INNER
    /\ LET n   == root
           m   == Min(free)
           r   == Min(free \ {m})
           med == Median(keysOf[n])
           lo  == {x \in keysOf[n] : x < med}
           up  == {x \in keysOf[n] : x > med}
       IN /\ m # r
          /\ keysOf' = [keysOf EXCEPT ![n] = lo, ![m] = up, ![r] = {med}]
          /\ childOf' = [x \in Nodes \X Keys |->
                           IF x = <<r, med>> THEN n
                           ELSE IF x[1] = m
                                THEN (IF x[2] \in up THEN childOf[n, x[2]]
                                                     ELSE NIL)
                           ELSE IF x[1] = n /\ x[2] \in (up \cup {med})
                                THEN NIL
                           ELSE childOf[x]]
          /\ lastOf' = [lastOf EXCEPT ![n] = childOf[n, med],
                                      ![m] = lastOf[n],
                                      ![r] = m]
          /\ isLeaf' = [isLeaf EXCEPT ![m] = FALSE, ![r] = FALSE]
          /\ root' = r
          /\ free' = free \ {m, r}
    /\ state' = FIND_LEAF_TO_ADD
    /\ UNCHANGED <<valOf, op, argKey, argVal, ret, expected, focus, parent,
                   path, dict>>

AddToLeaf ==
    /\ state = ADD_TO_LEAF
    /\ keysOf' = [keysOf EXCEPT ![focus] = @ \cup {argKey}]
    /\ valOf' = [valOf EXCEPT ![focus, argKey] = argVal]
    /\ dict' = [dict EXCEPT ![argKey] = argVal]
    /\ ret' = "ok"
    /\ state' = READY
    /\ focus' = NIL
    /\ parent' = NIL
    /\ path' = <<>>
    /\ UNCHANGED <<isLeaf, childOf, lastOf, root, free, op, argKey, argVal,
                   expected>>

---------------------------------------------------------------------------
(* Update *)

UpdateLeaf ==
    /\ state = UPDATE_LEAF
    /\ LET l == FindLeafFrom(root, argKey)
       IN IF argKey \in keysOf[l]
          THEN /\ valOf' = [valOf EXCEPT ![l, argKey] = argVal]
               /\ dict' = [dict EXCEPT ![argKey] = argVal]
               /\ ret' = "ok"
          ELSE /\ ret' = "error"
               /\ UNCHANGED <<valOf, dict>>
    /\ state' = READY
    /\ UNCHANGED <<isLeaf, keysOf, childOf, lastOf, root, free, op, argKey,
                   argVal, expected, focus, parent, path>>

---------------------------------------------------------------------------
(* Specification *)

Internal ==
    \/ GetValue
    \/ FindLeafToAdd
    \/ WhichToSplit
    \/ SplitLeaf
    \/ SplitInner
    \/ SplitRootLeaf
    \/ SplitRootInner
    \/ AddToLeaf
    \/ UpdateLeaf

Requests ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)

Next == Requests \/ Internal

Spec == Init /\ [][Next]_vars /\ WF_vars(Internal)

---------------------------------------------------------------------------
(* Invariants *)

TypeOk ==
    /\ isLeaf   \in [Nodes -> BOOLEAN]
    /\ keysOf   \in [Nodes -> SUBSET Keys]
    /\ childOf  \in [Nodes \X Keys -> Nodes \cup {NIL}]
    /\ lastOf   \in [Nodes -> Nodes \cup {NIL}]
    /\ valOf    \in [Nodes \X Keys -> Vals \cup {NIL}]
    /\ root     \in Nodes
    /\ free     \subseteq Nodes
    /\ root \notin free
    /\ state    \in States
    /\ op       \in Ops
    /\ argKey   \in Keys \cup {NIL}
    /\ argVal   \in Vals \cup {NIL}
    /\ ret      \in RetVals
    /\ expected \in RetVals
    /\ focus    \in Nodes \cup {NIL}
    /\ parent   \in Nodes \cup {NIL}
    /\ path     \in Seq(Nodes)
    /\ dict     \in [Keys -> Vals \cup {MISSING}]
    /\ \A n \in Nodes : Cardinality(keysOf[n]) <= MaxOccupancy

InUse == Nodes \ free

InnersMustHaveLast ==
    \A n \in InUse :
        ~isLeaf[n] =>
            /\ lastOf[n] \in InUse
            /\ \A k \in keysOf[n] : childOf[n, k] \in InUse

LeavesCantHaveLast ==
    \A n \in Nodes : isLeaf[n] => lastOf[n] = NIL

KeyOrderPreserved ==
    \A n \in InUse :
        ~isLeaf[n] =>
            /\ \A k \in keysOf[n] :
                 \A ck \in ChildKeys(childOf[n, k]) :
                    /\ ck < k
                    /\ \A k2 \in keysOf[n] : k2 < k => k2 <= ck
            /\ \A ck \in ChildKeys(lastOf[n]) :
                 \A k \in keysOf[n] : k <= ck

KeysInLeavesAreUnique ==
    \A n1, n2 \in InUse :
        (isLeaf[n1] /\ isLeaf[n2] /\ n1 # n2) =>
            keysOf[n1] \cap keysOf[n2] = {}

FreeNodesRemain == free # {}

\* Functional refinement: in quiescent states the tree denotes the
\* abstract map, and the last response matches the abstract map's response
\* (except when an insert is refused because of bounded resources).
TreeRefinesMap ==
    state = READY => \A k \in Keys : AbsMap[k] = dict[k]

ResponsesMatchMap ==
    (state = READY /\ op # "none") =>
        \/ ret = expected
        \/ (op = "insert" /\ ret = "out_of_space")

\* Progress: every started operation eventually returns to quiescence.
Progress == (state # READY) ~> (state = READY)

=============================================================================
```