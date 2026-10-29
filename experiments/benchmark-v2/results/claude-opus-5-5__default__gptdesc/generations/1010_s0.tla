```tla
(toSplit))
    /\ LET n == toSplit
           p == ParentOf(n)
           K == keysOf[n]
           s == Median(K)
           L == {k \in K : k < s}
           U == {k \in K : k > s}
       IN \E m \in FreeNodes :
           /\ keysOf' = [keysOf EXCEPT ![n] = L, ![m] = U, ![p] = @ \cup {s}]
           /\ isLeaf' = [isLeaf EXCEPT ![m] = FALSE]
           /\ childOf' = [childOf EXCEPT
                            ![p] = NewParentChildren(p, n, m, s),
                            ![n] = RestrictChildren(childOf[n], L),
                            ![m] = RestrictChildren(childOf[n], U)]
           /\ lastOf' = [lastOf EXCEPT ![p] = IF @ = n THEN m ELSE @,
                                       ![n] = childOf[n][s],
                                       ![m] = lastOf[n]]
           /\ UNCHANGED valOf
    /\ UNCHANGED root
    /\ FinishSplit

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v) \/ UpdateReq(k, v)
    \/ GetNext
    \/ FindLeafDescend
    \/ InsertExisting
    \/ InsertIntoLeaf
    \/ InsertFullLeaf
    \/ UpdateExisting
    \/ UpdateMissing
    \/ SplitRootLeaf
    \/ SplitRootInner
    \/ SplitParentFirst
    \/ SplitNonRootLeaf
    \/ SplitNonRootInner

Spec == Init /\ [][Next]_vars /\ WF_vars(GetNext)

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ root \in Nodes
    /\ isLeaf \in [Nodes -> BOOLEAN]
    /\ keysOf \in [Nodes -> SUBSET Keys]
    /\ childOf \in [Nodes -> [Keys -> Nodes \cup {NIL}]]
    /\ lastOf \in [Nodes -> Nodes \cup {NIL}]
    /\ valOf \in [Nodes -> [Keys -> Vals \cup {Missing}]]
    /\ focus \in Nodes \cup {NIL}
    /\ toSplit \in Nodes \cup {NIL}
    /\ op \in Ops \cup {NIL}
    /\ args \in {<<>>} \cup {<<k>> : k \in Keys}
                       \cup {<<k, v>> : k \in Keys, v \in Vals}
    /\ ret \in Vals \cup {Missing, NIL, "ok", "error"}
    /\ state \in States

-----------------------------------------------------------------------------
(* Structural invariants *)

\* No node holds more than MaxKeys keys
KeysBounded ==
    \A n \in Nodes : Cardinality(keysOf[n]) <= MaxKeys

\* Inner nodes are non-empty and have all child pointers defined
InnerNodesWellFormed ==
    \A n \in Nodes : ~isLeaf[n] =>
        /\ keysOf[n] # {}
        /\ lastOf[n] \in Nodes
        /\ \A k \in keysOf[n] : childOf[n][k] \in Nodes

\* Every key stored in a leaf has a value
LeafKeysHaveValues ==
    \A n \in Nodes : isLeaf[n] =>
        \A k \in Keys : (k \in keysOf[n]) <=> (valOf[n][k] \in Vals)

\* A key appears in at most one leaf
KeyInAtMostOneLeaf ==
    \A k \in Keys : \A n1, n2 \in Nodes :
        (isLeaf[n1] /\ isLeaf[n2] /\ k \in keysOf[n1] /\ k \in keysOf[n2])
            => n1 = n2

\* The root is never a child of any node
RootHasNoParent ==
    \A n \in Nodes : root \notin Children(n)

\* Each node has at most one parent
AtMostOneParent ==
    \A n, p1, p2 \in Nodes :
        (n \in Children(p1) /\ n \in Children(p2)) => p1 = p2

\* Search-tree ordering between inner nodes and their direct children
KeysOrdered ==
    \A n \in Nodes : ~isLeaf[n] =>
        /\ \A k \in keysOf[n] :
              childOf[n][k] \in Nodes =>
                  \A j \in keysOf[childOf[n][k]] : j < k
        /\ (keysOf[n] # {} /\ lastOf[n] \in Nodes) =>
              \A j \in keysOf[lastOf[n]] : j >= Max(keysOf[n])

\* All non-root leaves in use are non-empty
NonRootLeavesNonEmpty ==
    \A n \in InUse : (isLeaf[n] /\ n # root) => keysOf[n] # {}

-----------------------------------------------------------------------------
(* Liveness *)

\* Every get request eventually receives a response
GetEventuallyResponds == (state = "get") ~> (state = "ready")

-----------------------------------------------------------------------------
(* Refinement mapping to the abstract kvstore specification *)

\* The abstract dictionary is the union of the leaves' contents
Dict ==
    [k \in Keys |->
        IF \E n \in Nodes : isLeaf[n] /\ k \in keysOf[n]
        THEN valOf[CHOOSE n \in Nodes : isLeaf[n] /\ k \in keysOf[n]][k]
        ELSE Missing]

AbsState == IF state = "ready" THEN "ready" ELSE "working"

kvVars == <<Dict, op, args, ret, AbsState>>

(* Abstract kvstore spec, stated over the mapped state functions *)

KVInit ==
    /\ Dict = [k \in Keys |-> Missing]
    /\ op = NIL
    /\ args = <<>>
    /\ ret = NIL
    /\ AbsState = "ready"

KVGetReq(k) ==
    /\ AbsState = "ready"
    /\ op' = "get"
    /\ args' = <<k>>
    /\ ret' = NIL
    /\ AbsState' = "working"
    /\ UNCHANGED Dict

KVInsertReq(k, v) ==
    /\ AbsState = "ready"
    /\ op' = "insert"
    /\ args' = <<k, v>>
    /\ ret' = NIL
    /\ AbsState' = "working"
    /\ UNCHANGED Dict

KVUpdateReq(k, v) ==
    /\ AbsState = "ready"
    /\ op' = "update"
    /\ args' = <<k, v>>
    /\ ret' = NIL
    /\ AbsState' = "working"
    /\ UNCHANGED Dict

KVGetResp ==
    /\ AbsState = "working"
    /\ op = "get"
    /\ ret' = Dict[args[1]]
    /\ AbsState' = "ready"
    /\ UNCHANGED <<Dict, op, args>>

KVInsertResp ==
    /\ AbsState = "working"
    /\ op = "insert"
    /\ IF Dict[args[1]] = Missing
       THEN /\ Dict' = [Dict EXCEPT ![args[1]] = args[2]]
            /\ ret' = "ok"
       ELSE /\ UNCHANGED Dict
            /\ ret' = "error"
    /\ AbsState' = "ready"
    /\ UNCHANGED <<op, args>>

KVUpdateResp ==
    /\ AbsState = "working"
    /\ op = "update"
    /\ IF Dict[args[1]] # Missing
       THEN /\ Dict' = [Dict EXCEPT ![args[1]] = args[2]]
            /\ ret' = "ok"
       ELSE /\ UNCHANGED Dict
            /\ ret' = "error"
    /\ AbsState' = "ready"
    /\ UNCHANGED <<op, args>>

KVNext ==
    \/ \E k \in Keys : KVGetReq(k)
    \/ \E k \in Keys, v \in Vals : KVInsertReq(k, v) \/ KVUpdateReq(k, v)
    \/ KVGetResp
    \/ KVInsertResp
    \/ KVUpdateResp

KVSpec == KVInit /\ [][KVNext]_kvVars

THEOREM Refinement == Spec => KVSpec

THEOREM Safety == Spec => [](/\ TypeOK
                             /\ KeysBounded
                             /\ InnerNodesWellFormed
                             /\ LeafKeysHaveValues
                             /\ KeyInAtMostOneLeaf
                             /\ RootHasNoParent
                             /\ AtMostOneParent
                             /\ KeysOrdered
                             /\ NonRootLeavesNonEmpty)

THEOREM Liveness == Spec => GetEventuallyResponds

=============================================================================
```