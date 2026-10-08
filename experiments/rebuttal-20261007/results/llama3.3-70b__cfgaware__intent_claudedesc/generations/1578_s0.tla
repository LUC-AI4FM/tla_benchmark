------------------------------- MODULE DequeSpec -------------------------------
EXTENDS Integers, TLC

CONSTANT Null, MaxNodes, NumProcs
VARIABLE nodes, head, tail, freeList, procs, valuesPushed

defaultInitValue == <<Null, Null, Null, {x \in 1..MaxNodes : x != Null}, 
                     <<>>, {}>>

TypeInvariant ==
  /\ nodes \in [1..MaxNodes -> [left: 1..MaxNodes, right: 1..MaxNodes, val: Int]]
  /\ head \in 1..MaxNodes
  /\ tail \in 1..MaxNodes
  /\ freeList \subseteq 1..MaxNodes
  /\ procs \in [1..NumProcs -> <<>>]
  /\ valuesPushed \subseteq Int

PushLeft(p, v) ==
  /\ nodes[head].left = Null
  /\ freeList /= {}
  /\ LET n == CHOOSE x \in freeList : TRUE
      node == [left |-> Null, right |-> head, val |-> v]
   IN
     /\ nodes' = [nodes EXCEPT ![n] = node]
     /\ head' = n
     /\ freeList' = freeList \ {n}
     /\ procs' = [procs EXCEPT ![p] = <<PushLeft, okay>>]
     /\ valuesPushed' = valuesPushed \cup {v}

PushRight(p, v) ==
  /\ nodes[tail].right = Null
  /\ freeList /= {}
  /\ LET n == CHOOSE x \in freeList : TRUE
      node == [left |-> tail, right |-> Null, val |-> v]
   IN
     /\ nodes' = [nodes EXCEPT ![n] = node]
     /\ tail' = n
     /\ freeList' = freeList \ {n}
     /\ procs' = [procs EXCEPT ![p] = <<PushRight, okay>>]
     /\ valuesPushed' = valuesPushed \cup {v}

PopLeft(p) ==
  /\ nodes[head].left /= Null
  /\ LET v == nodes[nodes[head].left].val
      n == nodes[head].left
   IN
     /\ nodes' = [nodes EXCEPT ![n] = Null]
     /\ head' = nodes[head].left
     /\ freeList' = freeList \cup {n}
     /\ procs' = [procs EXCEPT ![p] = <<PopLeft, v>>]
     /\ valuesPushed' = valuesPushed \ {v}

PopRight(p) ==
  /\ nodes[tail].right /= Null
  /\ LET v == nodes[nodes[tail].right].val
      n == nodes[tail].right
   IN
     /\ nodes' = [nodes EXCEPT ![n] = Null]
     /\ tail' = nodes[tail].right
     /\ freeList' = freeList \cup {n}
     /\ procs' = [procs EXCEPT ![p] = <<PopRight, v>>]
     /\ valuesPushed' = valuesPushed \ {v}

Next ==
  \/ \E p \in 1..NumProcs :
      \/ \E v \in Int : PushLeft(p, v)
      \/ \E v \in Int : PushRight(p, v)
      \/ PopLeft(p)
      \/ PopRight(p)

Spec == Init /\ [][Next]_<<nodes, head, tail, freeList, procs, valuesPushed>>

THEOREM Spec => []TypeInvariant
=============================================================================