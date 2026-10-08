------------------------------- MODULE DequeSpec -------------------------------

CONSTANTS Val, NumSlots

VARIABLES head, tail, slots, freeList, gcState

(* Define a sentinel node that marks the ends of the deque *)
SENTINEL == <<NIL, NIL>>

(* Node structure: <<prev, next>> *)
Node(prev, next) == <<prev, next>>

(* Initialize the deque with sentinels and an empty free list *)
defaultInitValue ==
  LET initialSlots == [i \in 0..NumSlots-1 |-> SENTINEL]
      initialHeadTail == NumSlots - 1
  IN
    [head |-> initialHeadTail,
     tail |-> initialHeadTail,
     slots |-> initialSlots,
     freeList |-> {i \in 0..NumSlots-2}, (* Exclude the sentinel slot *)
     gcState |-> {}]

(* Check if a node is a sentinel *)
IsSentinel(node) == node = SENTINEL

(* Allocate a new node from the free list *)
AllocateNode() ==
  CHOOSE i \in freeList : i

(* Free a node back to the free list *)
FreeNode(i) ==
  freeList' = freeList \cup {i}

(* Push an element to the left end of the deque *)
PushLeft(val) ==
  /\ ~ (freeList = {})
  /\ LET newNode == AllocateNode()
     IN
       /\ slots'[newNode] = Node(head, SENTINEL)
       /\ slots'[head][1]' = newNode
       /\ head' = newNode
       /\ FreeNode(head)

(* Push an element to the right end of the deque *)
PushRight(val) ==
  /\ ~ (freeList = {})
  /\ LET newNode == AllocateNode()
     IN
       /\ slots'[newNode] = Node(SENTINEL, tail)
       /\ slots'[tail][2]' = newNode
       /\ tail' = newNode
       /\ FreeNode(tail)

(* Pop an element from the left end of the deque *)
PopLeft() ==
  /\ head # tail
  /\ LET oldHead == head
     IN
       /\ head' = slots[oldHead][2]
       /\ slots'[head'][1]' = NIL
       /\ slots'[oldHead] = SENTINEL
       /\ FreeNode(oldHead)

(* Pop an element from the right end of the deque *)
PopRight() ==
  /\ head # tail
  /\ LET oldTail == tail
     IN
       /\ tail' = slots[oldTail][1]
       /\ slots'[tail'][2]' = NIL
       /\ slots'[oldTail] = SENTINEL
       /\ FreeNode(oldTail)

(* Garbage collection: reclaim unreachable nodes *)
GarbageCollect() ==
  LET reachableNodes == {i \in 0..NumSlots-1 : Reachable(i)}
      newFreeList == (freeList \cup (DOMAIN slots) \ reachableNodes)
  IN
    freeList' = newFreeList

(* Check if a node is reachable from the head or tail *)
Reachable(nodeIndex) ==
  LET recCheck(index, visited) ==
        \/ index = NIL
        \/ index \in visited
        \/ LET prev == slots[index][1]
               next == slots[index][2]
           IN
             ~ (index \in visited)
             /\ recCheck(prev, visited \cup {index})
             /\ recCheck(next, visited \cup {index})
  IN
    recCheck(head, {}) \/ recCheck(tail, {})

(* Define the specification *)
Spec ==
  VARIABLES head, tail, slots, freeList, gcState
  INIT defaultInitValue
  NEXT
    \/ \E val \in Val : PushLeft(val)
    \/ \E val \in Val : PushRight(val)
    \/ PopLeft()
    \/ PopRight()
    \/ GarbageCollect()

(* Invariants *)
Inv ==
  /\ head \in DOMAIN slots
  /\ tail \in DOMAIN slots
  /\ IsSentinel(slots[head])
  /\ IsSentinel(slots[tail])
  /\ freeList \subseteq DOMAIN slots
  /\ \A i \in DOMAIN slots : ~ (IsSentinel(slots[i]) \/ i \in freeList) => Reachable(i)

(* Linearizability and safety properties are typically checked via TLC model checking *)
=============================================================================