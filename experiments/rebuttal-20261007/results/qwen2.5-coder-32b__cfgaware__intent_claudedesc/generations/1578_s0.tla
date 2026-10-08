------------------------------- MODULE LockFreeDeque -------------------------------

CONSTANTS 
    \* The set of all possible values that can be stored in the deque.
    Val,
    
    \* The initial value for the sentinel node's pointers.
    defaultInitValue,

    \* The maximum number of nodes in the memory pool.
    MaxNodes

VARIABLES
    \* The free list of available node addresses.
    freeList,
    
    \* The left and right sentinels of the deque.
    leftSentinel, rightSentinel,
    
    \* The memory pool where nodes are stored.
    memPool

\* Define a type for node addresses.
NodeAddr == 1..MaxNodes

\* Define a record type for nodes in the deque.
Node == [val: Val UNION {"nil"}, next: NodeAddr, prev: NodeAddr]

\* Initialize the memory pool with sentinel nodes and free list.
Init ==
    /\ freeList' = {2..MaxNodes}
    /\ leftSentinel' = 1
    /\ rightSentinel' = 1
    /\ memPool' = [n \in NodeAddr |-> 
        IF n = 1 THEN [val |-> "nil", next |-> defaultInitValue, prev |-> defaultInitValue]
        ELSE [val |-> "nil", next |-> defaultInitValue, prev |-> defaultInitValue]]

\* Allocate a node from the free list.
AllocateNode ==
    /\ \E addr \in freeList: TRUE
    /\ \/ /\ freeList' = freeList \ {CHOOSE addr \in freeList: TRUE}
         /\ memPool'[CHOOSE addr \in freeList: TRUE] = [val |-> "nil", next |-> defaultInitValue, prev |-> defaultInitValue]
       \/ freeList' = freeList
          /\ memPool' = memPool

\* Free a node back to the free list.
FreeNode(addr) ==
    /\ addr \notin freeList
    /\ freeList' = freeList \cup {addr}
    /\ memPool'[addr] = [val |-> "nil", next |-> defaultInitValue, prev |-> defaultInitValue]

\* Perform a double compare-and-swap operation.
DCAS(addr1, expectedVal1, newVal1, addr2, expectedVal2, newVal2) ==
    /\ memPool[addr1].next = expectedVal1
    /\ memPool[addr2].prev = expectedVal2
    /\ memPool' = [memPool EXCEPT ![addr1].next = newVal1, ![addr2].prev = newVal2]
    \/ memPool' = memPool

\* Push an element to the left end of the deque.
PushLeft(val) ==
    \E newAddr \in freeList: 
        /\ AllocateNode
        /\ DCAS(leftSentinel, memPool[leftSentinel].next, newAddr, memPool[leftSentinel].next, leftSentinel, leftSentinel)
        /\ memPool'[newAddr] = [val |-> val, next |-> memPool[leftSentinel].next, prev |-> leftSentinel]

\* Push an element to the right end of the deque.
PushRight(val) ==
    \E newAddr \in freeList: 
        /\ AllocateNode
        /\ DCAS(rightSentinel, memPool[rightSentinel].prev, newAddr, memPool[rightSentinel].prev, rightSentinel, rightSentinel)
        /\ memPool'[newAddr] = [val |-> val, next |-> rightSentinel, prev |-> memPool[rightSentinel].prev]

\* Pop an element from the left end of the deque.
PopLeft ==
    \E addr \in SUBSET NodeAddr:
        /\ addr /= defaultInitValue
        /\ DCAS(leftSentinel, memPool[leftSentinel].next, memPool[memPool[leftSentinel].next].next, memPool[memPool[leftSentinel].next].prev, leftSentinel, leftSentinel)
        /\ FreeNode(memPool[leftSentinel].next)

\* Pop an element from the right end of the deque.
PopRight ==
    \E addr \in SUBSET NodeAddr:
        /\ addr /= defaultInitValue
        /\ DCAS(rightSentinel, memPool[rightSentinel].prev, memPool[memPool[rightSentinel].prev].prev, memPool[memPool[rightSentinel].prev].next, rightSentinel, rightSentinel)
        /\ FreeNode(memPool[rightSentinel].prev)

\* The next state relation.
Next ==
    \/ \E val \in Val: PushLeft(val)
    \/ \E val \in Val: PushRight(val)
    \/ PopLeft
    \/ PopRight

\* The specification of the system.
Spec ==
    Init /\ [][Next]_<<leftSentinel, rightSentinel, freeList, memPool>>

=============================================================================