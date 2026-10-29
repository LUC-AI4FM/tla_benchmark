```tla
NCHANGED <<root, focus, op, args, ret>>

SplitRoot ==
    /\ state = "splitting"
    /\ focus = NIL
    /\ \E r, nn \in FreeNodes :
         /\ r # nn
         /\ DoSplit(r, root, nn, TRUE)
         /\ root' = r
         /\ focus' = r
    /\ state' = "searching"
    /\ toSplit' = NIL
    /\ UNCHANGED <<op, args, ret>>

\* No free nodes are available for a split: report capacity exhaustion
SplitFail ==
    /\ state = "splitting"
    /\ \/ focus = NIL /\ Cardinality(FreeNodes) < 2
       \/ focus # NIL /\ FreeNodes = {}
    /\ ret' = "full"
    /\ state' = "ready"
    /\ focus' = NIL
    /\ toSplit' = NIL
    /\ UNCHANGED <<treeVars, op, args>>

\* focus is a non-full leaf here
AddToLeaf ==
    /\ state = "adding"
    /\ LET k == args[1]
           v == args[2]
       IN IF k \in keysOf[focus]
            THEN /\ ret' = "error"
                 /\ UNCHANGED <<keysOf, valOf>>
            ELSE /\ keysOf' = [keysOf EXCEPT ![focus] = @ \cup {k}]
                 /\ valOf' = [valOf EXCEPT ![focus, k] = v]
                 /\ ret' = "ok"
    /\ state' = "ready"
    /\ focus' = NIL
    /\ UNCHANGED <<root, isLeaf, childOf, lastOf, toSplit, op, args>>

---------------------------------------------------------------------------
(* Delete is not implemented. *)

Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ GetDescend
    \/ GetResp
    \/ UpdateDescend
    \/ UpdateResp
    \/ InsertDescend
    \/ SplitChild
    \/ SplitRoot
    \/ SplitFail
    \/ AddToLeaf

Spec == Init /\ [][Next]_vars /\ WF_vars(GetStep)

---------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ root \in Nodes
    /\ isLeaf \in [Nodes -> BOOLEAN]
    /\ keysOf \in [Nodes -> SUBSET Keys]
    /\ childOf \in [Nodes \X Keys -> Nodes \cup {NIL}]
    /\ lastOf \in [Nodes -> Nodes \cup {NIL}]
    /\ valOf \in [Nodes \X Keys -> Vals \cup {NIL}]
    /\ focus \in Nodes \cup {NIL}
    /\ toSplit \in Nodes \cup {NIL}
    /\ op \in Ops \cup {NIL}
    /\ args \in {NIL} \cup {<<k>> : k \in Keys}
                      \cup {<<k, v>> : k \in Keys, v \in Vals}
    /\ ret \in RetVals
    /\ state \in States
```

```tla
---------------------------------------------------------------------------
(* Structural invariants *)

\* No node ever holds more than MaxKeys keys
KeysBounded ==
    \A n \in Nodes : Cardinality(keysOf[n]) <= MaxKeys

\* Every key in a used leaf has a value, and leaves have no child pointers
LeavesWellFormed ==
    \A n \in UsedLeaves :
        /\ \A k \in keysOf[n] : valOf[n, k] \in Vals
        /\ lastOf[n] = NIL
        /\ \A k \in Keys : childOf[n, k] = NIL

\* Every used inner node has keys, and its children are used nodes
InnerWellFormed ==
    \A n \in InUse :
        ~isLeaf[n] =>
            /\ keysOf[n] # {}
            /\ lastOf[n] \in InUse
            /\ \A k \in keysOf[n] : childOf[n, k] \in InUse

\* A key appears in at most one leaf
KeysInUniqueLeaf ==
    \A k \in Keys : \A n1, n2 \in UsedLeaves :
        (k \in keysOf[n1] /\ k \in keysOf[n2]) => n1 = n2

\* Ordering of separators relative to the keys of direct children
KeysOrdered ==
    \A n \in InUse :
        ~isLeaf[n] =>
            /\ \A s \in keysOf[n] :
                 childOf[n, s] \in Nodes =>
                    \A k \in keysOf[childOf[n, s]] : k < s
            /\ (lastOf[n] \in Nodes /\ keysOf[n] # {}) =>
                    \A k \in keysOf[lastOf[n]] : k >= Max(keysOf[n])

\* The root is always in use
RootInUse == root \in InUse

\* Outside of an insert, no split is pending
NoPendingSplit == state # "splitting" => toSplit = NIL

Invariants ==
    /\ TypeOK
    /\ KeysBounded
    /\ LeavesWellFormed
    /\ InnerWellFormed
    /\ KeysInUniqueLeaf
    /\ KeysOrdered
    /\ RootInUse
    /\ NoPendingSplit
```

```tla
---------------------------------------------------------------------------
(* Liveness: with weak fairness on get steps, every get completes *)

GetCompletes == (state # "ready" /\ op = "get") ~> (state = "ready")

---------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to the abstract kvstore specification.              *)
(* Abstract state: dict, absState, op, args, ret.                         *)
(***************************************************************************)

dict == [k \in Keys |->
            IF \E n \in UsedLeaves : k \in keysOf[n]
              THEN LET n == CHOOSE n \in UsedLeaves : k \in keysOf[n]
                   IN  valOf[n, k]
              ELSE Missing]

absState == IF state = "ready" THEN "ready" ELSE "working"

kvVars == <<dict, absState, op, args, ret>>

KVInit ==
    /\ dict = [k \in Keys |-> Missing]
    /\ absState = "ready"
    /\ op = NIL
    /\ args = NIL
    /\ ret = NIL

KVReq ==
    /\ absState = "ready"
    /\ absState' = "working"
    /\ dict' = dict
    /\ ret' = NIL
    /\ \/ \E k \in Keys : op' = "get" /\ args' = <<k>>
       \/ \E k \in Keys, v \in Vals :
            op' \in {"insert", "update"} /\ args' = <<k, v>>

KVResp ==
    /\ absState = "working"
    /\ absState' = "ready"
    /\ op' = op
    /\ args' = args
    /\ CASE op = "get" ->
              /\ ret' = dict[args[1]]
              /\ dict' = dict
         [] op = "insert" ->
              \/ /\ dict[args[1]] = Missing
                 /\ ret' = "ok"
                 /\ dict' = [dict EXCEPT ![args[1]] = args[2]]
              \/ /\ dict[args[1]] # Missing
                 /\ ret' = "error"
                 /\ dict' = dict
              \/ /\ ret' = "full"      \* capacity exhausted
                 /\ dict' = dict
         [] op = "update" ->
              \/ /\ dict[args[1]] # Missing
                 /\ ret' = "ok"
                 /\ dict' = [dict EXCEPT ![args[1]] = args[2]]
              \/ /\ dict[args[1]] = Missing
                 /\ ret' = "error"
                 /\ dict' = dict
         [] OTHER -> FALSE

KVNext == KVReq \/ KVResp

KVSpec == KVInit /\ [][KVNext]_kvVars

\* Checked as a temporal property
KVRefinement == KVSpec

THEOREM Spec => []Invariants
THEOREM Spec => GetCompletes
THEOREM Spec => KVSpec
=============================================================================
```