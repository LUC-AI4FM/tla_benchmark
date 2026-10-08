------------------------------- MODULE LockFreeDeque -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    MaxNodes \* Maximum number of nodes in the pool

VARIABLES 
    leftSentinel, rightSentinel, freeList, nodePool, nextPtr, prevPtr, values

Init == 
    /\ leftSentinel = 0
    /\ rightSentinel = 1
    /\ freeList = {2..MaxNodes}
    /\ nodePool = [n \in {0, 1} |-> <<0, 0>>] @ [n \in {2..MaxNodes} |-> <<0, 0>>]
    /\ nextPtr = [n \in {0, 1} |-> 1] @ [n \in {2..MaxNodes} |-> 0]
    /\ prevPtr = [n \in {0, 1} |-> 0] @ [n \in {2..MaxNodes} |-> 0]
    /\ values = [n \in {0, 1} |-> "sentinel"] @ [n \in {2..MaxNodes} |-> ""]
    
PushLeft(node, value) ==
    \/ freeList = {} -> "full"
    \/ /\ LET newHead == CHOOSE n \in freeList : TRUE
       IN /\ freeList' = freeList \ {newHead}
          /\ nodePool' = [nodePool EXCEPT ![newHead] = <<leftSentinel, nextPtr[leftSentinel]]>]
          /\ nextPtr' = [nextPtr EXCEPT ![leftSentinel] = newHead, ![newHead] = nextPtr[leftSentinel]]
          /\ prevPtr' = [prevPtr EXCEPT ![nextPtr[leftSentinel]] = newHead, ![newHead] = leftSentinel]
          /\ values' = [values EXCEPT ![newHead] = value]
          /\ UNCHANGED <<rightSentinel>>

PushRight(node, value) ==
    \/ freeList = {} -> "full"
    \/ /\ LET newTail == CHOOSE n \in freeList : TRUE
       IN /\ freeList' = freeList \ {newTail}
          /\ nodePool' = [nodePool EXCEPT ![newTail] = <<prevPtr[rightSentinel], rightSentinel>>]
          /\ nextPtr' = [nextPtr EXCEPT ![prevPtr[rightSentinel]] = newTail, ![newTail] = rightSentinel]
          /\ prevPtr' = [prevPtr EXCEPT ![rightSentinel] = newTail, ![newTail] = prevPtr[rightSentinel]]
          /\ values' = [values EXCEPT ![newTail] = value]
          /\ UNCHANGED <<leftSentinel>>

PopLeft(node) ==
    \/ nextPtr[leftSentinel] = rightSentinel -> "empty"
    \/ /\ LET oldHead == nextPtr[leftSentinel]
       IN /\ freeList' = freeList \cup {oldHead}
          /\ nodePool' = [nodePool EXCEPT ![oldHead] = <<0, 0>>]
          /\ nextPtr' = [nextPtr EXCEPT ![leftSentinel] = nextPtr[oldHead], ![prevPtr[nextPtr[oldHead]]] = leftSentinel]
          /\ prevPtr' = [prevPtr EXCEPT ![nextPtr[oldHead]] = 0]
          /\ values' = [values EXCEPT ![oldHead] = ""]
          /\ UNCHANGED <<rightSentinel>>

PopRight(node) ==
    \/ prevPtr[rightSentinel] = leftSentinel -> "empty"
    \/ /\ LET oldTail == prevPtr[rightSentinel]
       IN /\ freeList' = freeList \cup {oldTail}
          /\ nodePool' = [nodePool EXCEPT ![oldTail] = <<0, 0>>]
          /\ nextPtr' = [nextPtr EXCEPT ![prevPtr[oldTail]] = rightSentinel]
          /\ prevPtr' = [prevPtr EXCEPT ![rightSentinel] = prevPtr[oldTail], ![nextPtr[prevPtr[oldTail]]] = 0]
          /\ values' = [values EXCEPT ![oldTail] = ""]
          /\ UNCHANGED <<leftSentinel>>

Next == 
    \/ \E node, value \in freeList : PushLeft(node, value)
    \/ \E node, value \in freeList : PushRight(node, value)
    \/ \E node \in DOMAIN nextPtr : PopLeft(node) = "okay"
    \/ \E node \in DOMAIN prevPtr : PopRight(node) = "okay"

Spec == 
    /\ Init
    /\ [][Next]_<<leftSentinel, rightSentinel, freeList, nodePool, nextPtr, prevPtr, values>>
    /\ WF_[Next]_<<leftSentinel, rightSentinel, freeList, nodePool, nextPtr, prevPtr, values>>

Invariant1 == 
    \A n \in DOMAIN nextPtr : 
        \/ n = leftSentinel
        \/ n = rightSentinel
        \/ /\ nextPtr[n] \in DOMAIN nextPtr
           /\ prevPtr[nextPtr[n]] = n

Invariant2 ==
    \A n \in DOMAIN prevPtr :
        \/ n = leftSentinel
        \/ n = rightSentinel
        \/ /\ prevPtr[n] \in DOMAIN prevPtr
           /\ nextPtr[prevPtr[n]] = n

Invariant3 == 
    \A n \in DOMAIN values : 
        \/ n = leftSentinel
        \/ n = rightSentinel
        \/ values[n] \in {"sentinel"} \cup freeList

Invariant4 ==
    \A n \in DOMAIN nodePool :
        \/ n = leftSentinel
        \/ n = rightSentinel
        \/ /\ nodePool[n][1] \in DOMAIN nextPtr
           /\ nodePool[n][2] \in DOMAIN prevPtr

Invariant5 ==
    \A v \in {"sentinel"} \cup freeList : 
        \/ values[v] = "sentinel"
        \/ \E n \in DOMAIN values : values[n] = v

Invariant6 ==
    \A n \in DOMAIN nextPtr :
        \/ n = leftSentinel
        \/ n = rightSentinel
        \/ /\ LET path == [k \in 0..Len(NextPath(n))-1 |-> NextPath(n)[k]]
           IN /\ path[0] = n
              /\ path[LAST(path)] = rightSentinel
              /\ \A k \in 0..Len(path)-2 : nextPtr[path[k]] = path[k+1]

Invariant7 ==
    \A n \in DOMAIN prevPtr :
        \/ n = leftSentinel
        \/ n = rightSentinel
        \/ /\ LET path == [k \in 0..Len(PrevPath(n))-1 |-> PrevPath(n)[k]]
           IN /\ path[0] = n
              /\ path[LAST(path)] = leftSentinel
              /\ \A k \in 0..Len(path)-2 : prevPtr[path[k]] = path[k+1]

NextPath(n) ==
    LET recPath(k, p) == 
        IF nextPtr[k] = rightSentinel THEN p
        ELSE recPath(nextPtr[k], Append(p, <<nextPtr[k], values[nextPtr[k]]>>))
    IN recPath(n, <<n, values[n]>>)

PrevPath(n) ==
    LET recPath(k, p) == 
        IF prevPtr[k] = leftSentinel THEN p
        ELSE recPath(prevPtr[k], Append(p, <<prevPtr[k], values[prevPtr[k]]>>))
    IN recPath(n, <<n, values[n]>>)

Invariant8 ==
    \A n \in DOMAIN nextPtr :
        \/ n = leftSentinel
        \/ n = rightSentinel
        \/ /\ LET path == [k \in 0..Len(NextPath(n))-1 |-> NextPath(n)[k]]
           IN /\ \A k \in 0..Len(path)-2 : values[path[k]] # ""
              /\ values[path[LAST(path)]] = "sentinel"

Invariant9 ==
    \A n \in DOMAIN prevPtr :
        \/ n = leftSentinel
        \/ n = rightSentinel
        \/ /\ LET path == [k \in 0..Len(PrevPath(n))-1 |-> PrevPath(n)[k]]
           IN /\ \A k \in 0..Len(path)-2 : values[path[k]] # ""
              /\ values[path[LAST(path)]] = "sentinel"

Invariant10 ==
    \A v \in {"sentinel"} \cup freeList :
        \/ values[v] = "sentinel"
        \/ \E n \in DOMAIN values : values[n] = v

Spec == 
    /\ Init
    /\ [][Next]_<<leftSentinel, rightSentinel, freeList, nodePool, nextPtr, prevPtr, values>>
    /\ WF_[Next]_<<leftSentinel, rightSentinel, freeList, nodePool, nextPtr, prevPtr, values>>
    /\ \A s \in StateTrace : 
        /\ Invariant1[s]
        /\ Invariant2[s]
        /\ Invariant3[s]
        /\ Invariant4[s]
        /\ Invariant5[s]
        /\ Invariant6[s]
        /\ Invariant7[s]
        /\ Invariant8[s]
        /\ Invariant9[s]
        /\ Invariant10[s]

=============================================================================