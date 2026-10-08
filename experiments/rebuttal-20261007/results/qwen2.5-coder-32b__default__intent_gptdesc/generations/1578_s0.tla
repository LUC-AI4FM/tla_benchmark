------------------------------- MODULE ConcurrentDeque -------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    MaxNodes \* Maximum number of node slots

VARIABLES 
    head, tail, \* Pointers to the head and tail of the deque
    nodes,      \* Array of node records: [value |-> _, next |-> _, prev |-> _]
    freeSlots,  \* Set of indices representing free node slots
    gcState     \* State of the garbage collector

\* Node record type
Node == [value: STRING, next: Int, prev: Int]

\* Initial state
Init == 
    /\ head = -1
    /\ tail = -1
    /\ nodes = [i \in 0..MaxNodes-1 |-> <<NIL, -1, -1>>]
    /\ freeSlots = {0..MaxNodes-1}
    /\ gcState = {}

\* Allocate a new node slot
AllocateNode == 
    \/ freeSlots = {}
    \/ CHOOSE i \in freeSlots : 
        /\ freeSlots' = freeSlots \ {i}
        /\ nodes' = [nodes EXCEPT ![i] = <<NIL, -1, -1>>]
        /\ UNCHANGED head
        /\ UNCHANGED tail
        /\ UNCHANGED gcState

\* Free a node slot
FreeNode(i) ==
    /\ i \notin freeSlots
    /\ freeSlots' = freeSlots \cup {i}
    /\ nodes' = [nodes EXCEPT ![i] = <<NIL, -1, -1>>]
    /\ UNCHANGED head
    /\ UNCHANGED tail
    /\ UNCHANGED gcState

\* Push a value to the left end of the deque
PushLeft(value) ==
    \/ LET i == AllocateNode IN
        /\ i \notin freeSlots
        /\ nodes' = [nodes EXCEPT ![i] = <<value, head, -1>>]
        /\ IF head = -1 THEN tail' = i ELSE nodes'[head].prev' = i
        /\ head' = i
        /\ UNCHANGED freeSlots
        /\ UNCHANGED gcState

\* Push a value to the right end of the deque
PushRight(value) ==
    \/ LET i == AllocateNode IN
        /\ i \notin freeSlots
        /\ nodes' = [nodes EXCEPT ![i] = <<value, -1, tail>>]
        /\ IF tail = -1 THEN head' = i ELSE nodes'[tail].next' = i
        /\ tail' = i
        /\ UNCHANGED freeSlots
        /\ UNCHANGED gcState

\* Pop a value from the left end of the deque
PopLeft ==
    \/ head = -1
       /\ UNCHANGED nodes
       /\ UNCHANGED head
       /\ UNCHANGED tail
       /\ UNCHANGED freeSlots
       /\ UNCHANGED gcState
    \/ LET i == head IN
        /\ LET value == nodes[i].value IN
        /\ IF nodes[i].next = -1 THEN 
            head' = -1
            tail' = -1
           ELSE 
            head' = nodes[i].next
            nodes'[head'].prev' = -1
        /\ FreeNode(i)
        /\ UNCHANGED gcState

\* Pop a value from the right end of the deque
PopRight ==
    \/ tail = -1
       /\ UNCHANGED nodes
       /\ UNCHANGED head
       /\ UNCHANGED tail
       /\ UNCHANGED freeSlots
       /\ UNCHANGED gcState
    \/ LET i == tail IN
        /\ LET value == nodes[i].value IN
        /\ IF nodes[i].prev = -1 THEN 
            head' = -1
            tail' = -1
           ELSE 
            tail' = nodes[i].prev
            nodes'[tail'].next' = -1
        /\ FreeNode(i)
        /\ UNCHANGED gcState

\* Garbage collection step
GarbageCollect ==
    \/ gcState = {}
       /\ LET unreachable == {i \in 0..MaxNodes-1 : i \notin freeSlots /\ NOT ReachableFromHeadOrTail(i)} IN
       /\ gcState' = unreachable
    \/ LET i == CHOOSE j \in gcState : TRUE IN
        /\ FreeNode(i)
        /\ gcState' = gcState \ {i}
        /\ UNCHANGED head
        /\ UNCHANGED tail

\* Check if a node is reachable from the head or tail
ReachableFromHeadOrTail(i) ==
    \/ i = -1
    \/ ReachableFromHead(i)
    \/ ReachableFromTail(i)

\* Check if a node is reachable from the head
ReachableFromHead(i) ==
    LET rec(j) == j = i \/ (j \in 0..MaxNodes-1 /\ nodes[j].next # -1 /\ rec(nodes[j].next)) IN
    rec(head)

\* Check if a node is reachable from the tail
ReachableFromTail(i) ==
    LET rec(j) == j = i \/ (j \in 0..MaxNodes-1 /\ nodes[j].prev # -1 /\ rec(nodes[j].prev)) IN
    rec(tail)

\* Next state relation
Next ==
    \/ PushLeft(CHOICE {"value1", "value2", "value3"})
    \/ PushRight(CHOICE {"value1", "value2", "value3"})
    \/ PopLeft
    \/ PopRight
    \/ GarbageCollect

\* Specification
Spec == Init /\ [][Next]_<<head, tail, nodes, freeSlots, gcState>>

\* Invariants
Inv ==
    /\ \A i \in 0..MaxNodes-1 : 
        (i \notin freeSlots => nodes[i].value # NIL)
    /\ \A i \in 0..MaxNodes-1 :
        (nodes[i].next = -1 \/ nodes[nodes[i].next].prev = i)
    /\ \A i \in 0..MaxNodes-1 :
        (nodes[i].prev = -1 \/ nodes[nodes[i].prev].next = i)
    /\ head = -1 => tail = -1
    /\ tail = -1 => head = -1

\* Liveness properties
WF == WF_<<head, tail, nodes, freeSlots, gcState>>(Next)

\* Fairness conditions
FairPushLeft ==
    \A value \in {"value1", "value2", "value3"} : 
        <>[](\E i \in 0..MaxNodes-1 : i \notin freeSlots /\ PushLeft(value))

FairPushRight ==
    \A value \in {"value1", "value2", "value3"} : 
        <>[](\E i \in 0..MaxNodes-1 : i \notin freeSlots /\ PushRight(value))

FairPopLeft ==
    <>[](head # -1 => PopLeft)

FairPopRight ==
    <>[](tail # -1 => PopRight)

FairGarbageCollect ==
    <>[](\A i \in gcState : FreeNode(i))

\* Complete specification with invariants and fairness
CompleteSpec == Spec /\ Inv /\ WF /\ FairPushLeft /\ FairPushRight /\ FairPopLeft /\ FairPopRight /\ FairGarbageCollect

=============================================================================