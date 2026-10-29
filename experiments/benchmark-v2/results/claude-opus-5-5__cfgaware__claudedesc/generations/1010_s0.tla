---------------------------- MODULE btree ----------------------------
(***************************************************************************)
(* A B-tree supporting get, insert and update. Node splitting is modeled   *)
(* as a multi-step process. Deletions are not implemented.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Vals,
          MaxOccupancy,
          MaxNode,
          MaxKey,
          NIL,
          MISSING,
          READY,
          GET_VALUE,
          FIND_LEAF_TO_ADD,
          WHICH_TO_SPLIT,
          ADD_TO_LEAF,
          SPLIT_LEAF,
          SPLIT_INNER,
          SPLIT_ROOT_LEAF,
          SPLIT_ROOT_INNER,
          UPDATE_LEAF

Nodes == 1..MaxNode
Keys  == 1..MaxKey

States == {READY, GET_VALUE, FIND_LEAF_TO_ADD, WHICH_TO_SPLIT, ADD_TO_LEAF,
           SPLIT_LEAF, SPLIT_INNER, SPLIT_ROOT_LEAF, SPLIT_ROOT_INNER,
           UPDATE_LEAF}

VARIABLES isLeaf,   \* isLeaf[n] : is node n a leaf
          keysOf,   \* keysOf[n] : set of keys in node n
          childOf,  \* childOf[n, k] : child of inner node n holding keys < k
          lastOf,   \* lastOf[n] : child of inner node n holding keys >= max key
          valOf,    \* valOf[n, k] : value of key k in leaf n
          root,
          op,
          args,
          ret,
          focus,
          toSplit,
          state

vars == <<isLeaf, keysOf, childOf, lastOf, valOf, root,
          op, args, ret, focus, toSplit, state>>

treeVars == <<isLeaf, keysOf, childOf, lastOf, valOf, root>>

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)
Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

IsFull(n) == Cardinality(keysOf[n]) >= MaxOccupancy

FreeNodes == {n \in Nodes : ~isLeaf[n] /\ lastOf[n] = NIL /\ n # root}

Leaves == {n \in Nodes : isLeaf[n]}

Inners == {n \in Nodes : ~isLeaf[n] /\ lastOf[n] # NIL}

ChildrenOf(n) == {childOf[n, k] : k \in keysOf[n]} \cup {lastOf[n]}

ParentOf(n) == CHOOSE p \in Inners : n \in ChildrenOf(p)

RECURSIVE FindLeaf(_, _)
FindLeaf(n, key) ==
    IF isLeaf[n] THEN n
    ELSE LET bigger == {k \in keysOf[n] : key < k}
         IN IF bigger = {} THEN FindLeaf(lastOf[n], key)
                           ELSE FindLeaf(childOf[n, Min(bigger)], key)

KeysInTree == UNION {keysOf[n] : n \in Leaves}

LeafWith(k) == CHOOSE n \in Leaves : k \in keysOf[n]

\* pivot for splitting a leaf: lower half gets |K| \div 2 keys
LeafPivot(K) == CHOOSE p \in K : Cardinality({k \in K : k < p}) = Cardinality(K) \div 2

\* pivot for splitting an inner node: the pivot key is promoted
InnerPivot(K) == CHOOSE p \in K : Cardinality({k \in K : k < p}) = (Cardinality(K) - 1) \div 2

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ root = 1
    /\ isLeaf = [n \in Nodes |-> n = 1]
    /\ keysOf = [n \in Nodes |-> {}]
    /\ childOf = [n \in Nodes, k \in Keys |-> NIL]
    /\ lastOf = [n \in Nodes |-> NIL]
    /\ valOf = [n \in Nodes, k \in Keys |-> NIL]
    /\ op = NIL
    /\ args = <<>>
    /\ ret = NIL
    /\ focus = NIL
    /\ toSplit = <<>>
    /\ state = READY

(***************************************************************************)
(* Get                                                                     *)
(***************************************************************************)
GetReq(key) ==
    /\ state = READY
    /\ op' = "get"
    /\ args' = <<key>>
    /\ ret' = NIL
    /\ focus' = root
    /\ state' = GET_VALUE
    /\ UNCHANGED <<treeVars, toSplit>>

GetValue ==
    /\ state = GET_VALUE
    /\ LET key  == args[1]
           leaf == FindLeaf(root, key)
       IN /\ focus' = leaf
          /\ ret' = IF key \in keysOf[leaf] THEN valOf[leaf, key] ELSE MISSING
    /\ state' = READY
    /\ UNCHANGED <<treeVars, op, args, toSplit>>

(***************************************************************************)
(* Insert                                                                  *)
(***************************************************************************)
InsertReq(key, val) ==
    /\ state = READY
    /\ key \notin KeysInTree
    /\ op' = "insert"
    /\ args' = <<key, val>>
    /\ ret' = NIL
    /\ focus' = root
    /\ state' = FIND_LEAF_TO_ADD
    /\ UNCHANGED <<treeVars, toSplit>>

FindLeafToAdd ==
    /\ state = FIND_LEAF_TO_ADD
    /\ LET leaf == FindLeaf(root, args[1])
       IN /\ focus' = leaf
          /\ IF IsFull(leaf)
                THEN /\ state' = WHICH_TO_SPLIT
                     /\ toSplit' = <<leaf>>
                ELSE /\ state' = ADD_TO_LEAF
                     /\ toSplit' = <<>>
    /\ UNCHANGED <<treeVars, op, args, ret>>

WhichToSplit ==
    /\ state = WHICH_TO_SPLIT
    /\ LET n == Head(toSplit)
       IN IF n = root
            THEN /\ state' = IF isLeaf[root] THEN SPLIT_ROOT_LEAF ELSE SPLIT_ROOT_INNER
                 /\ UNCHANGED toSplit
            ELSE LET p == ParentOf(n)
                 IN IF IsFull(p)
                      THEN /\ toSplit' = <<p>> \o toSplit
                           /\ UNCHANGED state
                      ELSE /\ state' = IF isLeaf[n] THEN SPLIT_LEAF ELSE SPLIT_INNER
                           /\ UNCHANGED toSplit
    /\ UNCHANGED <<treeVars, op, args, ret, focus>>

AfterSplit ==
    /\ toSplit' = Tail(toSplit)
    /\ state' = IF Tail(toSplit) = <<>>
                  THEN FIND_LEAF_TO_ADD
                  ELSE IF isLeaf[Head(Tail(toSplit))] THEN SPLIT_LEAF ELSE SPLIT_INNER

SplitLeaf ==
    /\ state = SPLIT_LEAF
    /\ LET n   == Head(toSplit)
           p   == ParentOf(n)
           K   == keysOf[n]
           piv == LeafPivot(K)
           lo  == {k \in K : k < piv}
           hi  == K \ lo
       IN \E m \in FreeNodes :
            /\ isLeaf' = [isLeaf EXCEPT ![m] = TRUE]
            /\ keysOf' = [keysOf EXCEPT ![m] = lo, ![n] = hi, ![p] = @ \cup {piv}]
            /\ valOf' = [x \in Nodes, k \in Keys |->
                           IF x = m THEN (IF k \in lo THEN valOf[n, k] ELSE NIL)
                           ELSE IF x = n /\ k \in lo THEN NIL
                           ELSE valOf[x, k]]
            /\ childOf' = [childOf EXCEPT ![p, piv] = m]
            /\ UNCHANGED <<lastOf, root>>
    /\ AfterSplit
    /\ UNCHANGED <<op, args, ret, focus>>

SplitInner ==
    /\ state = SPLIT_INNER
    /\ LET n   == Head(toSplit)
           p   == ParentOf(n)
           K   == keysOf[n]
           piv == InnerPivot(K)
           lo  == {k \in K : k < piv}
           hi  == {k \in K : k > piv}
       IN \E m \in FreeNodes :
            /\ keysOf' = [keysOf EXCEPT ![m] = lo, ![n] = hi, ![p] = @ \cup {piv}]
            /\ childOf' = [x \in Nodes, k \in Keys |->
                             IF x = m THEN (IF k \in lo THEN childOf[n, k] ELSE NIL)
                             ELSE IF x = n THEN (IF k \in hi THEN childOf[n, k] ELSE NIL)
                             ELSE IF x = p /\ k = piv THEN m
                             ELSE childOf[x, k]]
            /\ lastOf' = [lastOf EXCEPT ![m] = childOf[n, piv]]
            /\ UNCHANGED <<isLeaf, valOf, root>>
    /\ AfterSplit
    /\ UNCHANGED <<op, args, ret, focus>>

SplitRootLeaf ==
    /\ state = SPLIT_ROOT_LEAF
    /\ LET r   == root
           K   == keysOf[r]
           piv == LeafPivot(K)
           lo  == {k \in K : k < piv}
           hi  == K \ lo
       IN \E m1, m2 \in FreeNodes :
            /\ m1 # m2
            /\ isLeaf' = [isLeaf EXCEPT ![r] = FALSE, ![m1] = TRUE, ![m2] = TRUE]
            /\ keysOf' = [keysOf EXCEPT ![r] = {piv}, ![m1] = lo, ![m2] = hi]
            /\ valOf' = [x \in Nodes, k \in Keys |->
                           IF x = m1 THEN (IF k \in lo THEN valOf[r, k] ELSE NIL)
                           ELSE IF x = m2 THEN (IF k \in hi THEN valOf[r, k] ELSE NIL)
                           ELSE IF x = r THEN NIL
                           ELSE valOf[x, k]]
            /\ childOf' = [childOf EXCEPT ![r, piv] = m1]
            /\ lastOf' = [lastOf EXCEPT ![r] = m2]
            /\ UNCHANGED root
    /\ AfterSplit
    /\ UNCHANGED <<op, args, ret, focus>>

SplitRootInner ==
    /\ state = SPLIT_ROOT_INNER
    /\ LET r   == root
           K   == keysOf[r]
           piv == InnerPivot(K)
           lo  == {k \in K : k < piv}
           hi  == {k \in K : k > piv}
       IN \E m1, m2 \in FreeNodes :
            /\ m1 # m2
            /\ keysOf' = [keysOf EXCEPT ![r] = {piv}, ![m1] = lo, ![m2] = hi]
            /\ childOf' = [x \in Nodes, k \in Keys |->
                             IF x = m1 THEN (IF k \in lo THEN childOf[r, k] ELSE NIL)
                             ELSE IF x = m2 THEN (IF k \in hi THEN childOf[r, k] ELSE NIL)
                             ELSE IF x = r THEN (IF k = piv THEN m1 ELSE NIL)
                             ELSE childOf[x, k]]
            /\ lastOf' = [lastOf EXCEPT ![r] = m2,
                                        ![m1] = childOf[r, piv],
                                        ![m2] = lastOf[r]]
            /\ UNCHANGED <<isLeaf, valOf, root>>
    /\ AfterSplit
    /\ UNCHANGED <<op, args, ret, focus>>

AddToLeaf ==
    /\ state = ADD_TO_LEAF
    /\ LET key  == args[1]
           val  == args[2]
           leaf == focus
       IN /\ keysOf' = [keysOf EXCEPT ![leaf] = @ \cup {key}]
          /\ valOf' = [valOf EXCEPT ![leaf, key] = val]
    /\ ret' = "ok"
    /\ state' = READY
    /\ UNCHANGED <<isLeaf, childOf, lastOf, root, op, args, focus, toSplit>>

(***************************************************************************)
(* Update                                                                  *)
(***************************************************************************)
UpdateReq(key, val) ==
    /\ state = READY
    /\ key \in KeysInTree
    /\ op' = "update"
    /\ args' = <<key, val>>
    /\ ret' = NIL
    /\ focus' = root
    /\ state' = UPDATE_LEAF
    /\ UNCHANGED <<treeVars, toSplit>>

UpdateLeaf ==
    /\ state = UPDATE_LEAF
    /\ LET key  == args[1]
           val  == args[2]
           leaf == FindLeaf(root, key)
       IN /\ focus' = leaf
          /\ valOf' = [valOf EXCEPT ![leaf, key] = val]
    /\ ret' = "ok"
    /\ state' = READY
    /\ UNCHANGED <<isLeaf, keysOf, childOf, lastOf, root, op, args, toSplit>>

(* Delete: not implemented *)

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Next ==
    \/ \E k \in Keys : GetReq(k)
    \/ GetValue
    \/ \E k \in Keys, v \in Vals : InsertReq(k, v)
    \/ FindLeafToAdd
    \/ WhichToSplit
    \/ SplitLeaf
    \/ SplitInner
    \/ SplitRootLeaf
    \/ SplitRootInner
    \/ AddToLeaf
    \/ \E k \in Keys, v \in Vals : UpdateReq(k, v)
    \/ UpdateLeaf

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOk ==
    /\ isLeaf \in [Nodes -> BOOLEAN]
    /\ keysOf \in [Nodes -> SUBSET Keys]
    /\ childOf \in [Nodes \X Keys -> Nodes \cup {NIL}]
    /\ lastOf \in [Nodes -> Nodes \cup {NIL}]
    /\ valOf \in [Nodes \X Keys -> Vals \cup {NIL}]
    /\ root \in Nodes
    /\ op \in {"get", "insert", "update", NIL}
    /\ args \in Seq(Keys \cup Vals)
    /\ ret \in Vals \cup {MISSING, NIL, "ok"}
    /\ focus \in Nodes \cup {NIL}
    /\ toSplit \in Seq(Nodes)
    /\ state \in States

InnersMustHaveLast ==
    \A n \in Nodes : (~isLeaf[n] /\ keysOf[n] # {}) => lastOf[n] # NIL

LeavesCantHaveLast ==
    \A n \in Nodes : isLeaf[n] => lastOf[n] = NIL

KeyOrderPreserved ==
    \A n \in Inners :
        /\ \A k \in keysOf[n] :
              childOf[n, k] # NIL =>
                \A x \in keysOf[childOf[n, k]] :
                    /\ x < k
                    /\ \A j \in keysOf[n] : j < k => x >= j
        /\ keysOf[n] # {} =>
              \A x \in keysOf[lastOf[n]] : x >= Max(keysOf[n])

KeysInLeavesAreUnique ==
    \A n1, n2 \in Leaves : n1 # n2 => keysOf[n1] \cap keysOf[n2] = {}

FreeNodesRemain == FreeNodes # {}

(***************************************************************************)
(* Refinement mapping to an abstract key-value store                       *)
(***************************************************************************)
Mapping == [k \in Keys |-> IF k \in KeysInTree THEN valOf[LeafWith(k), k] ELSE MISSING]

KVInit == Mapping = [k \in Keys |-> MISSING]

KVNext == \E k \in Keys, v \in Vals : Mapping' = [Mapping EXCEPT ![k] = v]

kvstore == KVInit /\ [][KVNext]_Mapping

Refinement == kvstore

THEOREM Spec => Refinement

=============================================================================