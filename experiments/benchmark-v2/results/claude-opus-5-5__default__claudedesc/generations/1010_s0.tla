```tla
Split) - 1) IN
    /\ toSplit' = rest
    /\ IF rest = <<>>
          THEN /\ state' = "FIND_LEAF_TO_ADD"
               /\ focus' = NIL
          ELSE /\ state' = IF isLeaf[rest[Len(rest)]] THEN "SPLIT_LEAF"
                                                       ELSE "SPLIT_INNER"
               /\ focus' = rest[Len(rest)]

SplitLeaf ==
    /\ state = "SPLIT_LEAF"
    /\ LET n     == focus
           p     == ParentOf(n)
           pivot == PivotOf(n)
           lo    == {x \in keysOf[n] : x < pivot}
           hi    == keysOf[n] \ lo
       IN \E m \in FreeNodes :
            /\ isLeaf' = [isLeaf EXCEPT ![m] = TRUE]
            /\ keysOf' = [keysOf EXCEPT ![n] = lo, ![m] = hi,
                                        ![p] = @ \cup {pivot}]
            /\ valOf' = [nk \in Nodes \X Keys |->
                           IF nk[1] = n /\ nk[2] \in hi THEN NIL
                           ELSE IF nk[1] = m
                                THEN IF nk[2] \in hi THEN valOf[n, nk[2]]
                                                     ELSE NIL
                                ELSE valOf[nk]]
            /\ childOf' = ParentChild(childOf, p, n, m, pivot)
            /\ lastOf' = ParentLast(lastOf, p, n, m)
    /\ AfterSplit
    /\ UNCHANGED <<root, op, args, ret>>

SplitInner ==
    /\ state = "SPLIT_INNER"
    /\ LET n     == focus
           p     == ParentOf(n)
           pivot == PivotOf(n)
           lo    == {x \in keysOf[n] : x < pivot}
           hi    == {x \in keysOf[n] : x > pivot}
       IN \E m \in FreeNodes :
            /\ isLeaf' = [isLeaf EXCEPT ![m] = FALSE]
            /\ keysOf' = [keysOf EXCEPT ![n] = lo, ![m] = hi,
                                        ![p] = @ \cup {pivot}]
            /\ childOf' = ParentChild(
                   [nk \in Nodes \X Keys |->
                      IF nk[1] = n
                         THEN IF nk[2] \in lo THEN childOf[nk] ELSE NIL
                      ELSE IF nk[1] = m
                         THEN IF nk[2] \in hi THEN childOf[n, nk[2]] ELSE NIL
                      ELSE childOf[nk]],
                   p, n, m, pivot)
            /\ lastOf' = ParentLast(
                   [lastOf EXCEPT ![n] = childOf[n, pivot],
                                  ![m] = lastOf[n]],
                   p, n, m)
            /\ UNCHANGED valOf
    /\ AfterSplit
    /\ UNCHANGED <<root, op, args, ret>>

SplitRootLeaf ==
    /\ state = "SPLIT_ROOT_LEAF"
    /\ LET pivot == PivotOf(root)
           lo    == {x \in keysOf[root] : x < pivot}
           hi    == keysOf[root] \ lo
       IN \E a, b \in FreeNodes :
            /\ a # b
            /\ isLeaf' = [isLeaf EXCEPT ![root] = FALSE, ![a] = TRUE,
                                        ![b] = TRUE]
            /\ keysOf' = [keysOf EXCEPT ![root] = {pivot}, ![a] = lo,
                                        ![b] = hi]
            /\ valOf' = [nk \in Nodes \X Keys |->
                           IF nk[1] = root THEN NIL
                           ELSE IF nk[1] = a
                              THEN IF nk[2] \in lo THEN valOf[root, nk[2]]
                                                   ELSE NIL
                           ELSE IF nk[1] = b
                              THEN IF nk[2] \in hi THEN valOf[root, nk[2]]
                                                   ELSE NIL
                           ELSE valOf[nk]]
            /\ childOf' = [childOf EXCEPT ![root, pivot] = a]
            /\ lastOf' = [lastOf EXCEPT ![root] = b]
    /\ AfterSplit
    /\ UNCHANGED <<root, op, args, ret>>

SplitRootInner ==
    /\ state = "SPLIT_ROOT_INNER"
    /\ LET pivot == PivotOf(root)
           lo    == {x \in keysOf[root] : x < pivot}
           hi    == {x \in keysOf[root] : x > pivot}
       IN \E a, b \in FreeNodes :
            /\ a # b
            /\ isLeaf' = [isLeaf EXCEPT ![a] = FALSE, ![b] = FALSE]
            /\ keysOf' = [keysOf EXCEPT ![root] = {pivot}, ![a] = lo,
                                        ![b] = hi]
            /\ childOf' = [nk \in Nodes \X Keys |->
                             IF nk[1] = root
                                THEN IF nk[2] = pivot THEN a ELSE NIL
                             ELSE IF nk[1] = a
                                THEN IF nk[2] \in lo THEN childOf[root, nk[2]]
                                                     ELSE NIL
                             ELSE IF nk[1] = b
                                THEN IF nk[2] \in hi THEN childOf[root, nk[2]]
                                                     ELSE NIL
                             ELSE childOf[nk]]
            /\ lastOf' = [lastOf EXCEPT ![root] = b,
                                        ![a] = childOf[root, pivot],
                                        ![b] = lastOf[root]]
            /\ UNCHANGED valOf
    /\ AfterSplit
    /\ UNCHANGED <<root, op, args, ret>>

AddToLeaf ==
    /\ state = "ADD_TO_LEAF"
    /\ keysOf' = [keysOf EXCEPT ![focus] = @ \cup {args[1]}]
    /\ valOf' = [valOf EXCEPT ![focus, args[1]] = args[2]]
    /\ ret' = "ok"
    /\ focus' = NIL
    /\ state' = "READY"
    /\ UNCHANGED <<isLeaf, childOf, lastOf, root, op, args, toSplit>>

-----------------------------------------------------------------------------
(* Update *)

UpdateReq(k, v) ==
    /\ state = "READY"
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ ret' = NIL
    /\ focus' = FindLeaf(root, k)
    /\ state' = "UPDATE_LEAF"
    /\ UNCHANGED <<treeVars, toSplit>>

UpdateLeaf ==
    /\ state = "UPDATE_LEAF"
    /\ IF args[1] \in keysOf[focus]
          THEN /\ valOf' = [valOf EXCEPT ![focus, args[1]] = args[2]]
               /\ ret' = "ok"
          ELSE /\ valOf' = valOf
               /\ ret' = "error"
    /\ focus' = NIL
    /\ state' = "READY"
    /\ UNCHANGED <<isLeaf, keysOf, childOf, lastOf, root, op, args, toSplit>>

\* Deletions are not implemented.

-----------------------------------------------------------------------------
Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ GetValue
    \/ FindLeafToAdd
    \/ WhichToSplit
    \/ SplitLeaf
    \/ SplitInner
    \/ SplitRootLeaf
    \/ SplitRootInner
    \/ AddToLeaf
    \/ UpdateLeaf

Fairness ==
    /\ WF_vars(GetValue)
    /\ WF_vars(FindLeafToAdd)
    /\ WF_vars(WhichToSplit)
    /\ WF_vars(SplitLeaf)
    /\ WF_vars(SplitInner)
    /\ WF_vars(SplitRootLeaf)
    /\ WF_vars(SplitRootInner)
    /\ WF_vars(AddToLeaf)
    /\ WF_vars(UpdateLeaf)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

InnersMustHaveLast ==
    \A n \in Nodes : (~isLeaf[n] /\ n \in InUse) => lastOf[n] # NIL

LeavesCantHaveLast ==
    \A n \in Nodes : isLeaf[n] => lastOf[n] = NIL

KeyOrderPreserved ==
    \A n \in Nodes : (~isLeaf[n] /\ keysOf[n] # {}) =>
        /\ \A k \in keysOf[n] :
              childOf[n, k] \in Nodes =>
                  \A x \in keysOf[childOf[n, k]] : x < k
        /\ \A k1, k2 \in keysOf[n] :
              (k1 < k2 /\ childOf[n, k2] \in Nodes) =>
                  \A x \in keysOf[childOf[n, k2]] : x >= k1
        /\ lastOf[n] \in Nodes =>
              \A x \in keysOf[lastOf[n]] : \A k \in keysOf[n] : x >= k

LeafKeysUnique ==
    \A n1, n2 \in Nodes :
        (n1 # n2 /\ isLeaf[n1] /\ isLeaf[n2]) =>
            keysOf[n1] \cap keysOf[n2] = {}

FreeNodeAlwaysAvailable == FreeNodes # {}

(* Liveness *)

OperationsComplete == (state # "READY") ~> (state = "READY")

-----------------------------------------------------------------------------
(* Refinement mapping to the abstract key-value store *)

AbsDict ==
    [k \in Keys |->
        IF \E n \in Nodes : isLeaf[n] /\ k \in keysOf[n]
           THEN valOf[CHOOSE n \in Nodes : isLeaf[n] /\ k \in keysOf[n], k]
           ELSE MISSING]

AbsState == IF state = "READY" THEN "ready" ELSE "working"

Mapping == INSTANCE kvstore WITH Keys <- Keys, Vals <- Vals,
                                 MISSING <- MISSING, NIL <- NIL,
                                 dict <- AbsDict, op <- op, args <- args,
                                 ret <- ret, state <- AbsState

Refinement == Mapping!Spec

THEOREM Spec => Refinement
=============================================================================
```