------------------------------- MODULE btree -------------------------------
(***************************************************************************)
(* A B-tree (B+-tree flavour: all key/value pairs live in leaves) based   *)
(* key-value store supporting get, insert and update requests over a      *)
(* bounded set of keys, values and nodes.                                  *)
(*                                                                         *)
(* The tree structure is represented explicitly with:                      *)
(*   keysOf  : the set of keys held by each node                           *)
(*   childOf : childOf[n,k] is the child of n holding keys < k             *)
(*   lastOf  : lastOf[n] is the child of n holding keys >= Max(keysOf[n])  *)
(*   isLeaf  : leaf flag of each node                                      *)
(*   valOf   : the value stored for each key                               *)
(*                                                                         *)
(* A small request/response interface (op, args, ret, state) is shared    *)
(* with an abstract kvstore specification, and a refinement mapping to     *)
(* that abstract specification is given below.                             *)
(*                                                                         *)
(* There is no fault model.  NOTE: deletes are not implemented.            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Keys,          \* set of keys (natural numbers, totally ordered)
          Vals,          \* set of values
          Nodes,         \* set of available tree nodes
          MaxOccupancy,  \* maximum number of keys in a node
          NIL,           \* null pointer / no value
          Missing        \* returned by get when the key is absent

ASSUME /\ Keys \subseteq Nat
       /\ MaxOccupancy \in Nat
       /\ MaxOccupancy >= 3
       /\ NIL \notin Nodes
       /\ NIL \notin Vals
       /\ Missing \notin Vals
       /\ Missing # NIL

VARIABLES root,     \* the root node
          isLeaf,   \* [Nodes -> BOOLEAN]
          keysOf,   \* [Nodes -> SUBSET Keys]
          childOf,  \* [Nodes \X Keys -> Nodes \cup {NIL}]
          lastOf,   \* [Nodes -> Nodes \cup {NIL}]
          valOf,    \* [Keys -> Vals \cup {NIL}]
          op,       \* current request type
          args,     \* current request arguments
          ret,      \* response value
          state,    \* operational state: "ready", "findLeaf", "split"
          focus     \* node currently being examined

treeVars == <<root, isLeaf, keysOf, childOf, lastOf>>
vars == <<root, isLeaf, keysOf, childOf, lastOf, valOf,
          op, args, ret, state, focus>>

Ops == {"get", "insert", "update"}
States == {"ready", "findLeaf", "split"}

-----------------------------------------------------------------------------
(* Helpers *)

Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Nodes currently part of the tree
InUse == ({root} \cup {childOf[nk] : nk \in Nodes \X Keys}
                 \cup {lastOf[n] : n \in Nodes}) \ {NIL}

Free == Nodes \ InUse

\* The parent of a non-root node
ParentOf(n) == CHOOSE p \in InUse :
                  \/ \E k \in keysOf[p] : childOf[p, k] = n
                  \/ lastOf[p] = n

\* Child of internal node n that should contain key k
ChildFor(n, k) ==
    IF k >= Max(keysOf[n])
    THEN lastOf[n]
    ELSE childOf[n, Min({x \in keysOf[n] : k < x})]

\* Median key used when splitting
PivotOf(S) == CHOOSE p \in S :
                 Cardinality({x \in S : x < p}) = Cardinality(S) \div 2

IsFull(n) == Cardinality(keysOf[n]) >= MaxOccupancy

-----------------------------------------------------------------------------
(* Refinement mapping to the abstract kvstore *)

dict == [k \in Keys |->
           IF \E n \in InUse : isLeaf[n] /\ k \in keysOf[n]
           THEN valOf[k]
           ELSE Missing]

AState == IF state = "ready" THEN "ready" ELSE "working"

absVars == <<op, args, ret, AState, dict>>

KVInit == /\ op = NIL
          /\ args = <<>>
          /\ ret = NIL
          /\ AState = "ready"
          /\ dict = [k \in Keys |-> Missing]

KVGetReq == /\ AState = "ready"
            /\ \E k \in Keys : /\ op' = "get"
                               /\ args' = <<k>>
            /\ ret' = NIL
            /\ AState' = "working"
            /\ dict' = dict

KVInsertReq == /\ AState = "ready"
               /\ \E k \in Keys, v \in Vals : /\ op' = "insert"
                                              /\ args' = <<k, v>>
               /\ ret' = NIL
               /\ AState' = "working"
               /\ dict' = dict

KVUpdateReq == /\ AState = "ready"
               /\ \E k \in Keys, v \in Vals : /\ op' = "update"
                                              /\ args' = <<k, v>>
               /\ ret' = NIL
               /\ AState' = "working"
               /\ dict' = dict

KVGetResp == /\ AState = "working"
             /\ op = "get"
             /\ ret' = dict[args[1]]
             /\ AState' = "ready"
             /\ dict' = dict
             /\ op' = op
             /\ args' = args

KVInsertResp == /\ AState = "working"
                /\ op = "insert"
                /\ IF dict[args[1]] = Missing
                   THEN /\ dict' = [dict EXCEPT ![args[1]] = args[2]]
                        /\ ret' = "ok"
                   ELSE /\ dict' = dict
                        /\ ret' = "error"
                /\ AState' = "ready"
                /\ op' = op
                /\ args' = args

KVUpdateResp == /\ AState = "working"
                /\ op = "update"
                /\ IF dict[args[1]] # Missing
                   THEN /\ dict' = [dict EXCEPT ![args[1]] = args[2]]
                        /\ ret' = "ok"
                   ELSE /\ dict' = dict
                        /\ ret' = "error"
                /\ AState' = "ready"
                /\ op' = op
                /\ args' = args

KVNext == \/ KVGetReq \/ KVInsertReq \/ KVUpdateReq
          \/ KVGetResp \/ KVInsertResp \/ KVUpdateResp

KVSpecBar == KVInit /\ [][KVNext]_absVars

-----------------------------------------------------------------------------
(* Initial state *)

Init == /\ root \in Nodes
        /\ isLeaf = [n \in Nodes |-> TRUE]
        /\ keysOf = [n \in Nodes |-> {}]
        /\ childOf = [nk \in Nodes \X Keys |-> NIL]
        /\ lastOf = [n \in Nodes |-> NIL]
        /\ valOf = [k \in Keys |-> NIL]
        /\ op = NIL
        /\ args = <<>>
        /\ ret = NIL
        /\ state = "ready"
        /\ focus = NIL

-----------------------------------------------------------------------------
(* Requests *)

GetReq(k) == /\ state = "ready"
             /\ op' = "get"
             /\ args' = <<k>>
             /\ ret' = NIL
             /\ state' = "findLeaf"
             /\ focus' = root
             /\ UNCHANGED <<treeVars, valOf>>

InsertReq(k, v) == /\ state = "ready"
                   /\ op' = "insert"
                   /\ args' = <<k, v>>
                   /\ ret' = NIL
                   /\ state' = "findLeaf"
                   /\ focus' = root
                   /\ UNCHANGED <<treeVars, valOf>>

UpdateReq(k, v) == /\ state = "ready"
                   /\ op' = "update"
                   /\ args' = <<k, v>>
                   /\ ret' = NIL
                   /\ state' = "findLeaf"
                   /\ focus' = root
                   /\ UNCHANGED <<treeVars, valOf>>

-----------------------------------------------------------------------------
(* Searching *)

FindLeafStep == /\ state = "findLeaf"
                /\ ~isLeaf[focus]
                /\ focus' = ChildFor(focus, args[1])
                /\ UNCHANGED <<treeVars, valOf, op, args, ret, state>>

GetAtLeaf == /\ state = "findLeaf"
             /\ op = "get"
             /\ isLeaf[focus]
             /\ ret' = IF args[1] \in keysOf[focus]
                       THEN valOf[args[1]] ELSE Missing
             /\ state' = "ready"
             /\ focus' = NIL
             /\ UNCHANGED <<treeVars, valOf, op, args>>

-----------------------------------------------------------------------------
(* Adding *)

InsertAtLeaf ==
    /\ state = "findLeaf"
    /\ op = "insert"
    /\ isLeaf[focus]
    /\ LET k == args[1]
           v == args[2]
       IN CASE k \in keysOf[focus] ->
                 /\ ret' = "error"
                 /\ state' = "ready"
                 /\ focus' = NIL
                 /\ UNCHANGED <<treeVars, valOf>>
            [] ~IsFull(focus) ->
                 /\ keysOf' = [keysOf EXCEPT ![focus] = @ \cup {k}]
                 /\ valOf' = [valOf EXCEPT ![k] = v]
                 /\ ret' = "ok"
                 /\ state' = "ready"
                 /\ focus' = NIL
                 /\ UNCHANGED <<root, isLeaf, childOf, lastOf>>
            [] OTHER ->
                 /\ state' = "split"
                 /\ UNCHANGED <<treeVars, valOf, ret, focus>>
    /\ UNCHANGED <<op, args>>

UpdateAtLeaf ==
    /\ state = "findLeaf"
    /\ op = "update"
    /\ isLeaf[focus]
    /\ LET k == args[1]
           v == args[2]
       IN IF k \in keysOf[focus]
          THEN /\ valOf' = [valOf EXCEPT ![k] = v]
               /\ ret' = "ok"
          ELSE /\ ret' = "error"
               /\ UNCHANGED valOf
    /\ state' = "ready"
    /\ focus' = NIL
    /\ UNCHANGED <<treeVars, op, args>>

-----------------------------------------------------------------------------
(* Splitting *)

\* Split full node n into n (lower half) and fresh node m (upper half),
\* inserting the pivot into parent pp (a fresh root if isNewRoot).
SplitAction(n, m, pp, isNewRoot) ==
    LET P      == PivotOf(keysOf[n])
        leaf   == isLeaf[n]
        nKeys  == {x \in keysOf[n] : x < P}
        mKeys  == IF leaf THEN {x \in keysOf[n] : x >= P}
                          ELSE {x \in keysOf[n] : x > P}
        ppOld  == IF isNewRoot THEN {} ELSE keysOf[pp]
        ppLast == IF isNewRoot THEN m
                  ELSE IF lastOf[pp] = n THEN m ELSE lastOf[pp]
        ppChild(k) == IF k = P THEN n
                      ELSE IF isNewRoot THEN NIL
                      ELSE IF k \in keysOf[pp] /\ childOf[pp, k] = n THEN m
                      ELSE childOf[pp, k]
    IN /\ keysOf' = [keysOf EXCEPT ![n] = nKeys, ![m] = mKeys,
                                   ![pp] = ppOld \cup {P}]
       /\ isLeaf' = [isLeaf EXCEPT ![m] = leaf, ![pp] = FALSE]
       /\ lastOf' = [x \in Nodes |->
                       CASE x = n  -> IF leaf THEN NIL ELSE childOf[n, P]
                         [] x = m  -> IF leaf THEN NIL ELSE lastOf[n]
                         [] x = pp -> ppLast
                         [] OTHER  -> lastOf[x]]
       /\ childOf' = [nk \in Nodes \X Keys |->
                       LET x == nk[1]
                           k == nk[2]
                       IN CASE x = n  -> IF ~leaf /\ k < P
                                         THEN childOf[n, k] ELSE NIL
                            [] x = m  -> IF ~leaf /\ k > P /\ k \in keysOf[n]
                                         THEN childOf[n, k] ELSE NIL
                            [] x = pp -> ppChild(k)
                            [] OTHER  -> childOf[x, k]]
       /\ root' = IF isNewRoot THEN pp ELSE root

SplitStep ==
    /\ state = "split"
    /\ IF focus = root
       THEN \E m, r \in Free :
               /\ m # r
               /\ SplitAction(focus, m, r, TRUE)
               /\ state' = "findLeaf"
               /\ focus' = r
       ELSE LET p == ParentOf(focus) IN
            IF IsFull(p)
            THEN /\ focus' = p          \* split the parent first
                 /\ UNCHANGED <<treeVars, state>>
            ELSE \E m \in Free :
                    /\ SplitAction(focus, m, p, FALSE)
                    /\ state' = "findLeaf"
                    /\ focus' = root    \* restart search after split
    /\ UNCHANGED <<valOf, op, args, ret>>

-----------------------------------------------------------------------------
(* Specification *)

GetStep == (op = "get" /\ FindLeafStep) \/ GetAtLeaf

Next == \/ \E k \in Keys : GetReq(k)
        \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
        \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
        \/ FindLeafStep
        \/ GetAtLeaf
        \/ InsertAtLeaf
        \/ UpdateAtLeaf
        \/ SplitStep

Spec == Init /\ [][Next]_vars /\ WF_vars(GetStep)

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ root \in Nodes
    /\ isLeaf \in [Nodes -> BOOLEAN]
    /\ keysOf \in [Nodes -> SUBSET Keys]
    /\ childOf \in [Nodes \X Keys -> Nodes \cup {NIL}]
    /\ lastOf \in [Nodes -> Nodes \cup {NIL}]
    /\ valOf \in [Keys -> Vals \cup {NIL}]
    /\ op \in Ops \cup {NIL}
    /\ args \in {<<>>} \cup [1..1 -> Keys] \cup (Keys \X Vals)
    /\ ret \in Vals \cup {Missing, "ok", "error", NIL}
    /\ state \in States
    /\ focus \in Nodes \cup {NIL}

\* Occupancy bound on every node in the tree
BoundedOccupancy == \A n \in InUse : Cardinality(keysOf[n]) <= MaxOccupancy

\* Leaves have no children
LeavesHaveNoChildren ==
    \A n \in InUse : isLeaf[n] =>
        /\ lastOf[n] = NIL
        /\ \A k \in Keys : childOf[n, k] = NIL

\* Internal nodes are non-empty and have a child for every key plus a last child
InternalNodesHaveChildren ==
    \A n \in InUse : ~isLeaf[n] =>
        /\ keysOf[n] # {}
        /\ lastOf[n] # NIL
        /\ \A k \in keysOf[n] : childOf[n, k] # NIL

\* Child pointers only for keys actually held
NoDanglingChildPointers ==
    \A n \in InUse : \A k \in Keys \ keysOf[n] : childOf[n, k] = NIL

\* A key appears in at most one leaf
KeysInLeavesUnique ==
    \A n1, n2 \in InUse :
        (n1 # n2 /\ isLeaf[n1] /\ isLeaf[n2]) => keysOf[n1] \cap keysOf[n2] = {}

\* Search-tree ordering between a node and its children
ChildKeysOrdered ==
    \A n \in InUse : ~isLeaf[n] =>
        /\ \A k \in keysOf[n] :
              \A x \in keysOf[childOf[n, k]] : x < k
        /\ \A x \in keysOf[lastOf[n]] : x >= Max(keysOf[n])

\* Every key stored in a leaf has a value
StoredKeysHaveValues ==
    \A n \in InUse : isLeaf[n] => \A k \in keysOf[n] : valOf[k] \in Vals

-----------------------------------------------------------------------------
(* Liveness *)

GetsTerminate == (state # "ready" /\ op = "get") ~> (state = "ready")

-----------------------------------------------------------------------------
(* Refinement of the abstract kvstore *)

Refinement == KVSpecBar

THEOREM Spec => []TypeOK
THEOREM Spec => Refinement

=============================================================================