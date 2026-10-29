------------------------------- MODULE btree -------------------------------
(***************************************************************************)
(* A B-tree based key-value store supporting get, insert and update.       *)
(* Deletes are not implemented.                                            *)
(*                                                                         *)
(* Tree structure:                                                         *)
(*   keysOf[n]    : set of keys stored in node n                           *)
(*   childOf[n,k] : for an inner node, the child holding keys < k          *)
(*                  (and >= the previous key in n)                         *)
(*   lastOf[n]    : for an inner node, the child holding keys >= max key   *)
(*   isLeaf[n]    : whether node n is a leaf                               *)
(*   valOf[n,k]   : value stored for key k in leaf n                       *)
(*                                                                         *)
(* Assumes MaxOccupancy >= 2 and MaxNode >= 2.                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS READY, GET_VALUE, FIND_LEAF_TO_ADD, WHICH_TO_SPLIT, ADD_TO_LEAF,
          SPLIT_ROOT_LEAF, SPLIT_ROOT_INNER, SPLIT_INNER, SPLIT_LEAF,
          UPDATE_LEAF

CONSTANTS NIL, MISSING, Vals, MaxOccupancy, MaxNode, MaxKey

VARIABLES root, isLeaf, keysOf, childOf, lastOf, valOf,
          focus, op, args, ret, state

vars == <<root, isLeaf, keysOf, childOf, lastOf, valOf,
          focus, op, args, ret, state>>

Keys  == 1..MaxKey
Nodes == 1..MaxNode

States == {READY, GET_VALUE, FIND_LEAF_TO_ADD, WHICH_TO_SPLIT, ADD_TO_LEAF,
           SPLIT_ROOT_LEAF, SPLIT_ROOT_INNER, SPLIT_INNER, SPLIT_LEAF,
           UPDATE_LEAF}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Median(K) == CHOOSE k \in K : Cardinality({j \in K : j < k}) = Cardinality(K) \div 2

Children(p) == {childOf[p, k] : k \in keysOf[p]} \cup
               (IF lastOf[p] # NIL THEN {lastOf[p]} ELSE {})

ParentOf(n) == CHOOSE p \in Nodes : ~isLeaf[p] /\ n \in Children(p)

Full(n) == Cardinality(keysOf[n]) >= MaxOccupancy

FreeNodes == {n \in Nodes :
                /\ n # root
                /\ \A m \in Nodes : n \notin Children(m)}

ChildFor(n, k) ==
    LET bigger == {j \in keysOf[n] : k < j}
    IN IF bigger = {} THEN lastOf[n] ELSE childOf[n, Min(bigger)]

RECURSIVE FindLeaf(_, _)
FindLeaf(n, k) == IF isLeaf[n] THEN n ELSE FindLeaf(ChildFor(n, k), k)

RECURSIVE SplitTarget(_)
SplitTarget(n) ==
    IF n = root THEN n
    ELSE IF Full(ParentOf(n)) THEN SplitTarget(ParentOf(n))
    ELSE n

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ root = Min(Nodes)
    /\ isLeaf = [n \in Nodes |-> TRUE]
    /\ keysOf = [n \in Nodes |-> {}]
    /\ childOf = [x \in Nodes \X Keys |-> NIL]
    /\ lastOf = [n \in Nodes |-> NIL]
    /\ valOf = [x \in Nodes \X Keys |-> NIL]
    /\ focus = NIL
    /\ op = NIL
    /\ args = NIL
    /\ ret = NIL
    /\ state = READY

TreeUnchanged == UNCHANGED <<root, isLeaf, keysOf, childOf, lastOf, valOf>>

(***************************************************************************)
(* Requests                                                                *)
(***************************************************************************)
GetReq(key) ==
    /\ state = READY
    /\ op' = "get"
    /\ args' = <<key>>
    /\ ret' = NIL
    /\ focus' = FindLeaf(root, key)
    /\ state' = GET_VALUE
    /\ TreeUnchanged

InsertReq(key, val) ==
    /\ state = READY
    /\ op' = "insert"
    /\ args' = <<key, val>>
    /\ ret' = NIL
    /\ focus' = NIL
    /\ state' = FIND_LEAF_TO_ADD
    /\ TreeUnchanged

UpdateReq(key, val) ==
    /\ state = READY
    /\ op' = "update"
    /\ args' = <<key, val>>
    /\ ret' = NIL
    /\ focus' = FindLeaf(root, key)
    /\ state' = UPDATE_LEAF
    /\ TreeUnchanged

(***************************************************************************)
(* Get                                                                     *)
(***************************************************************************)
GetValue ==
    /\ state = GET_VALUE
    /\ LET key == args[1]
       IN ret' = IF key \in keysOf[focus] THEN valOf[focus, key] ELSE MISSING
    /\ state' = READY
    /\ focus' = NIL
    /\ UNCHANGED <<op, args>>
    /\ TreeUnchanged

(***************************************************************************)
(* Update                                                                  *)
(***************************************************************************)
UpdateLeaf ==
    /\ state = UPDATE_LEAF
    /\ LET key == args[1]
           val == args[2]
       IN IF key \in keysOf[focus]
          THEN /\ valOf' = [valOf EXCEPT ![focus, key] = val]
               /\ ret' = "ok"
          ELSE /\ UNCHANGED valOf
               /\ ret' = "error"
    /\ state' = READY
    /\ focus' = NIL
    /\ UNCHANGED <<op, args, root, isLeaf, keysOf, childOf, lastOf>>

(***************************************************************************)
(* Insert                                                                  *)
(***************************************************************************)
FindLeafToAdd ==
    /\ state = FIND_LEAF_TO_ADD
    /\ LET key  == args[1]
           leaf == FindLeaf(root, key)
       IN /\ focus' = leaf
          /\ IF key \in keysOf[leaf]
             THEN /\ ret' = "error"
                  /\ state' = READY
             ELSE /\ ret' = ret
                  /\ state' = IF Full(leaf) THEN WHICH_TO_SPLIT ELSE ADD_TO_LEAF
    /\ UNCHANGED <<op, args>>
    /\ TreeUnchanged

WhichToSplit ==
    /\ state = WHICH_TO_SPLIT
    /\ LET t    == SplitTarget(focus)
           need == IF t = root THEN 2 ELSE 1
       IN IF Cardinality(FreeNodes) > need
          THEN /\ focus' = t
               /\ ret' = ret
               /\ state' = IF t = root
                           THEN IF isLeaf[t] THEN SPLIT_ROOT_LEAF ELSE SPLIT_ROOT_INNER
                           ELSE IF isLeaf[t] THEN SPLIT_LEAF ELSE SPLIT_INNER
          ELSE /\ focus' = NIL
               /\ ret' = "error"
               /\ state' = READY
    /\ UNCHANGED <<op, args>>
    /\ TreeUnchanged

AddToLeaf ==
    /\ state = ADD_TO_LEAF
    /\ LET key == args[1]
           val == args[2]
       IN /\ keysOf' = [keysOf EXCEPT ![focus] = @ \cup {key}]
          /\ valOf' = [valOf EXCEPT ![focus, key] = val]
    /\ ret' = "ok"
    /\ state' = READY
    /\ focus' = NIL
    /\ UNCHANGED <<op, args, root, isLeaf, childOf, lastOf>>

SplitRootLeaf ==
    /\ state = SPLIT_ROOT_LEAF
    /\ LET n == focus
           r == Min(FreeNodes)
           s == Min(FreeNodes \ {r})
           m == Median(keysOf[n])
           L == {k \in keysOf[n] : k < m}
           R == keysOf[n] \ L
       IN /\ keysOf' = [keysOf EXCEPT ![n] = L, ![s] = R, ![r] = {m}]
          /\ valOf' = [x \in Nodes \X Keys |->
                         IF x[1] = s /\ x[2] \in R THEN valOf[n, x[2]] ELSE valOf[x]]
          /\ childOf' = [x \in Nodes \X Keys |->
                           IF x = <<r, m>> THEN n ELSE childOf[x]]
          /\ lastOf' = [lastOf EXCEPT ![r] = s]
          /\ isLeaf' = [isLeaf EXCEPT ![r] = FALSE]
          /\ root' = r
    /\ state' = FIND_LEAF_TO_ADD
    /\ focus' = NIL
    /\ UNCHANGED <<op, args, ret>>

SplitRootInner ==
    /\ state = SPLIT_ROOT_INNER
    /\ LET n == focus
           r == Min(FreeNodes)
           s == Min(FreeNodes \ {r})
           m == Median(keysOf[n])
           L == {k \in keysOf[n] : k < m}
           R == {k \in keysOf[n] : m < k}
       IN /\ keysOf' = [keysOf EXCEPT ![n] = L, ![s] = R, ![r] = {m}]
          /\ childOf' = [x \in Nodes \X Keys |->
                           IF x = <<r, m>> THEN n
                           ELSE IF x[1] = s /\ x[2] \in R THEN childOf[n, x[2]]
                           ELSE childOf[x]]
          /\ lastOf' = [lastOf EXCEPT ![r] = s, ![s] = lastOf[n], ![n] = childOf[n, m]]
          /\ isLeaf' = [isLeaf EXCEPT ![r] = FALSE, ![s] = FALSE]
          /\ root' = r
          /\ UNCHANGED valOf
    /\ state' = FIND_LEAF_TO_ADD
    /\ focus' = NIL
    /\ UNCHANGED <<op, args, ret>>

SplitLeaf ==
    /\ state = SPLIT_LEAF
    /\ LET n == focus
           p == ParentOf(n)
           s == Min(FreeNodes)
           m == Median(keysOf[n])
           L == {k \in keysOf[n] : k < m}
           R == keysOf[n] \ L
       IN /\ keysOf' = [keysOf EXCEPT ![n] = L, ![s] = R, ![p] = @ \cup {m}]
          /\ valOf' = [x \in Nodes \X Keys |->
                         IF x[1] = s /\ x[2] \in R THEN valOf[n, x[2]] ELSE valOf[x]]
          /\ childOf' = [x \in Nodes \X Keys |->
                           IF x = <<p, m>> THEN n
                           ELSE IF x[1] = p /\ x[2] \in keysOf[p] /\ childOf[x] = n THEN s
                           ELSE childOf[x]]
          /\ lastOf' = [lastOf EXCEPT ![p] = IF @ = n THEN s ELSE @]
          /\ UNCHANGED <<root, isLeaf>>
    /\ state' = FIND_LEAF_TO_ADD
    /\ focus' = NIL
    /\ UNCHANGED <<op, args, ret>>

SplitInner ==
    /\ state = SPLIT_INNER
    /\ LET n == focus
           p == ParentOf(n)
           s == Min(FreeNodes)
           m == Median(keysOf[n])
           L == {k \in keysOf[n] : k < m}
           R == {k \in keysOf[n] : m < k}
       IN /\ keysOf' = [keysOf EXCEPT ![n] = L, ![s] = R, ![p] = @ \cup {m}]
          /\ childOf' = [x \in Nodes \X Keys |->
                           IF x = <<p, m>> THEN n
                           ELSE IF x[1] = p /\ x[2] \in keysOf[p] /\ childOf[x] = n THEN s
                           ELSE IF x[1] = s /\ x[2] \in R THEN childOf[n, x[2]]
                           ELSE childOf[x]]
          /\ lastOf' = [lastOf EXCEPT ![p] = IF @ = n THEN s ELSE @,
                                      ![s] = lastOf[n],
                                      ![n] = childOf[n, m]]
          /\ isLeaf' = [isLeaf EXCEPT ![s] = FALSE]
          /\ UNCHANGED <<root, valOf>>
    /\ state' = FIND_LEAF_TO_ADD
    /\ focus' = NIL
    /\ UNCHANGED <<op, args, ret>>

(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ GetValue
    \/ UpdateLeaf
    \/ FindLeafToAdd
    \/ WhichToSplit
    \/ AddToLeaf
    \/ SplitRootLeaf
    \/ SplitRootInner
    \/ SplitLeaf
    \/ SplitInner

Spec == Init /\ [][Next]_vars /\ WF_vars(GetValue)

(***************************************************************************)
(* Refinement mapping to the abstract kvstore specification.               *)
(* The abstract store is a dictionary from keys to values (or MISSING).    *)
(* Mapping: dict is obtained by looking up each key in the tree.           *)
(*   KV == INSTANCE kvstore WITH dict <- dict, op <- op, args <- args,     *)
(*                              ret <- ret                                 *)
(***************************************************************************)
dict == [k \in Keys |->
           LET leaf == FindLeaf(root, k)
           IN IF k \in keysOf[leaf] THEN valOf[leaf, k] ELSE MISSING]

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOk ==
    /\ root \in Nodes
    /\ isLeaf \in [Nodes -> BOOLEAN]
    /\ keysOf \in [Nodes -> SUBSET Keys]
    /\ childOf \in [Nodes \X Keys -> Nodes \cup {NIL}]
    /\ lastOf \in [Nodes -> Nodes \cup {NIL}]
    /\ valOf \in [Nodes \X Keys -> Vals \cup {NIL}]
    /\ focus \in Nodes \cup {NIL}
    /\ op \in {"get", "insert", "update", NIL}
    /\ args \in {NIL} \cup {<<k>> : k \in Keys} \cup {<<k, v>> : k \in Keys, v \in Vals}
    /\ ret \in Vals \cup {"ok", "error", MISSING, NIL}
    /\ state \in States

InnersMustHaveLast ==
    \A n \in Nodes : ~isLeaf[n] => lastOf[n] # NIL

LeavesCantHaveLast ==
    \A n \in Nodes : isLeaf[n] => lastOf[n] = NIL

KeyOrderPreserved ==
    \A n \in Nodes : ~isLeaf[n] =>
        /\ \A k \in keysOf[n] :
              \A j \in keysOf[childOf[n, k]] :
                  /\ j < k
                  /\ \A i \in keysOf[n] : i < k => i <= j
        /\ \A j \in keysOf[lastOf[n]] : \A i \in keysOf[n] : i <= j

KeysInLeavesAreUnique ==
    \A n1, n2 \in Nodes :
        (n1 # n2 /\ isLeaf[n1] /\ isLeaf[n2]) => keysOf[n1] \cap keysOf[n2] = {}

FreeNodesRemain == FreeNodes # {}

=============================================================================