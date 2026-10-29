is full; switch to splitting. *)
InsertFull ==
    /\ state = "findLeaf"
    /\ op = "insert"
    /\ isLeaf[focus]
    /\ key \notin keysOf[focus]
    /\ Full(focus)
    /\ path' = Append(path, focus)
    /\ focus' = NIL
    /\ state' = "split"
    /\ UNCHANGED <<op, args, ret>>
    /\ UNCHANGED treeVars

-----------------------------------------------------------------------------
(* Splitting *)

(* Index in path of the topmost node of the run of full nodes that ends   *)
(* at the leaf. Its parent (if any) has room for one more separator.      *)
SplitIndex ==
    CHOOSE i \in 1..Len(path) :
        /\ \A j \in i..Len(path) : Full(path[j])
        /\ (i = 1 \/ ~Full(path[i - 1]))

(* Split node n into n (lower half) and new node m (upper half), pushing  *)
(* the separator into par. If rootSplit, par is a freshly allocated root. *)
SplitNode(n, par, m, rootSplit) ==
    LET ks  == keysOf[n]
        lo  == Lower(ks)
        sep == SepKey(ks)
        hi  == IF isLeaf[n] THEN ks \ lo ELSE UpperInner(ks)
    IN
    /\ keysOf' = [x \in Nodes |->
                    IF x = n THEN lo
                    ELSE IF x = m THEN hi
                    ELSE IF x = par THEN keysOf[x] \cup {sep}
                    ELSE keysOf[x]]
    /\ isLeaf' = [x \in Nodes |->
                    IF x = m THEN isLeaf[n]
                    ELSE IF x = par THEN FALSE
                    ELSE isLeaf[x]]
    /\ valOf' = [q \in Nodes \X Keys |->
                    IF q[1] = n /\ q[2] \in hi THEN NIL
                    ELSE IF q[1] = m /\ q[2] \in hi THEN valOf[n, q[2]]
                    ELSE valOf[q]]
    /\ childOf' = [q \in Nodes \X Keys |->
                    IF q[1] = n /\ q[2] \in ks \ lo THEN NIL
                    ELSE IF q[1] = m /\ q[2] \in hi THEN childOf[n, q[2]]
                    ELSE IF q[1] = par /\ q[2] = sep THEN n
                    ELSE IF q[1] = par /\ childOf[q] = n THEN m
                    ELSE childOf[q]]
    /\ lastOf' = [x \in Nodes |->
                    IF x = n THEN (IF isLeaf[n] THEN NIL ELSE childOf[n, sep])
                    ELSE IF x = m THEN lastOf[n]
                    ELSE IF x = par /\ (rootSplit \/ lastOf[x] = n) THEN m
                    ELSE lastOf[x]]
    /\ root' = IF rootSplit THEN par ELSE root
    /\ state' = "findLeaf"
    /\ focus' = IF rootSplit THEN par ELSE root
    /\ path' = <<>>
    /\ UNCHANGED <<op, args, ret>>

(* Not enough free nodes to split: report that the store is full. *)
SplitFail ==
    /\ Respond(FULL)
    /\ UNCHANGED treeVars

Split ==
    /\ state = "split"
    /\ LET i == SplitIndex
           n == path[i]
       IN IF i = 1
            THEN IF \E m, r \in Free : m # r
                   THEN \E m, r \in Free : m # r /\ SplitNode(n, r, m, TRUE)
                   ELSE SplitFail
            ELSE IF Free # {}
                   THEN \E m \in Free : SplitNode(n, path[i - 1], m, FALSE)
                   ELSE SplitFail

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ FindLeaf
    \/ GetResp
    \/ UpdateResp
    \/ InsertExisting
    \/ InsertAdd
    \/ InsertFull
    \/ Split

GetStep == op = "get" /\ (FindLeaf \/ GetResp)

Spec == Init /\ [][Next]_vars /\ WF_vars(GetStep)

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ root \in Nodes
    /\ isLeaf \in [Nodes -> BOOLEAN]
    /\ keysOf \in [Nodes -> SUBSET Keys]
    /\ childOf \in [Nodes \X Keys -> Nodes \cup {NIL}]
    /\ lastOf \in [Nodes -> Nodes \cup {NIL}]
    /\ valOf \in [Nodes \X Keys -> Vals \cup {NIL}]
    /\ focus \in Nodes \cup {NIL}
    /\ path \in Seq(Nodes)
    /\ op \in Ops \cup {NIL}
    /\ args \in {NIL} \cup {<<k>> : k \in Keys} \cup (Keys \X Vals)
    /\ ret \in Vals \cup {MISSING, NIL, OK, ERR, FULL}
    /\ state \in {"ready", "findLeaf", "split"}

OccupancyOK ==
    \A n \in Nodes : Cardinality(keysOf[n]) <= MaxKeys

FreeNodesClean ==
    \A n \in Free :
        /\ isLeaf[n]
        /\ keysOf[n] = {}
        /\ lastOf[n] = NIL
        /\ \A k \in Keys : childOf[n, k] = NIL /\ valOf[n, k] = NIL

LeavesHaveNoChildren ==
    \A n \in Nodes : isLeaf[n] =>
        /\ lastOf[n] = NIL
        /\ \A k \in Keys : childOf[n, k] = NIL

InnerNodesWellFormed ==
    \A n \in Used : ~isLeaf[n] =>
        /\ keysOf[n] # {}
        /\ lastOf[n] # NIL
        /\ \A k \in keysOf[n] : childOf[n, k] # NIL

ChildPointersOnlyForKeys ==
    \A n \in Nodes, k \in Keys : childOf[n, k] # NIL => k \in keysOf[n]

ValuesOnlyInLeaves ==
    \A n \in Nodes, k \in Keys :
        valOf[n, k] # NIL <=> (isLeaf[n] /\ k \in keysOf[n])

RootIsNotAChild ==
    /\ \A q \in Nodes \X Keys : childOf[q] # root
    /\ \A n \in Nodes : lastOf[n] # root

KeysUniqueInLeaves ==
    \A n1, n2 \in Leaves : n1 # n2 => keysOf[n1] \cap keysOf[n2] = {}

KeysOrdered ==
    \A n \in Used : ~isLeaf[n] =>
        /\ \A k \in keysOf[n] : \A j \in SubtreeKeys(childOf[n, k]) : j < k
        /\ \A j \in SubtreeKeys(lastOf[n]) : j >= Max(keysOf[n])

Balanced == Cardinality(LeafDepths(root)) = 1

StructuralInvariants ==
    /\ OccupancyOK
    /\ FreeNodesClean
    /\ LeavesHaveNoChildren
    /\ InnerNodesWellFormed
    /\ ChildPointersOnlyForKeys
    /\ ValuesOnlyInLeaves
    /\ RootIsNotAChild
    /\ KeysUniqueInLeaves
    /\ KeysOrdered
    /\ Balanced

-----------------------------------------------------------------------------
(* Liveness: every get request eventually receives a response. *)

GetTerminates ==
    [](op = "get" /\ state # "ready" => <>(state = "ready"))

-----------------------------------------------------------------------------
(* Refinement mapping to an abstract kvstore specification.               *)

dictMap ==
    [k \in Keys |->
        IF \E n \in Leaves : k \in keysOf[n]
          THEN valOf[CHOOSE n \in Leaves : k \in keysOf[n], k]
          ELSE MISSING]

stateMap == IF state = "ready" THEN "ready" ELSE "working"

kvVars == <<dictMap, op, args, ret, stateMap>>

KvInit ==
    /\ dictMap = [k \in Keys |-> MISSING]
    /\ op = NIL
    /\ args = NIL
    /\ ret = NIL
    /\ stateMap = "ready"

KvReq ==
    /\ stateMap = "ready"
    /\ \/ \E k \in Keys : op' = "get" /\ args' = <<k>>
       \/ \E k \in Keys, v \in Vals :
            op' \in {"insert", "update"} /\ args' = <<k, v>>
    /\ ret' = NIL
    /\ stateMap' = "working"
    /\ UNCHANGED dictMap

KvGetResp ==
    /\ stateMap = "working"
    /\ op = "get"
    /\ ret' = dictMap[args[1]]
    /\ stateMap' = "ready"
    /\ UNCHANGED <<dictMap, op, args>>

KvInsertResp ==
    /\ stateMap = "working"
    /\ op = "insert"
    /\ IF dictMap[args[1]] = MISSING
         THEN \/ /\ dictMap' = [dictMap EXCEPT ![args[1]] = args[2]]
                 /\ ret' = OK
              \/ /\ UNCHANGED dictMap
                 /\ ret' = FULL
         ELSE /\ UNCHANGED dictMap
              /\ ret' = ERR
    /\ stateMap' = "ready"
    /\ UNCHANGED <<op, args>>

KvUpdateResp ==
    /\ stateMap = "working"
    /\ op = "update"
    /\ IF dictMap[args[1]] # MISSING
         THEN /\ dictMap' = [dictMap EXCEPT ![args[1]] = args[2]]
              /\ ret' = OK
         ELSE /\ UNCHANGED dictMap
              /\ ret' = ERR
    /\ stateMap' = "ready"
    /\ UNCHANGED <<op, args>>

KvNext == KvReq \/ KvGetResp \/ KvInsertResp \/ KvUpdateResp

KvSpec == KvInit /\ [][KvNext]_kvVars

Refinement == KvSpec

THEOREM Spec => [](TypeOK /\ StructuralInvariants)
THEOREM Spec => Refinement
THEOREM Spec => GetTerminates

=============================================================================
```