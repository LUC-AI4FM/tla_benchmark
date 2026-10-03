---------------------------- MODULE ConcurrentDeque ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Procs,          \* Set of process identifiers
    Addresses,      \* Set of memory addresses
    Values,         \* Set of values that can be stored
    NullAddr        \* Special null address constant

VARIABLES
    mem,            \* Memory: mapping from addresses to node records
    leftHat,        \* Left hat pointer (head of deque from left)
    rightHat,       \* Right hat pointer (head of deque from right)
    freelist,       \* Set of free addresses for allocation
    pc,             \* Program counter for each process
    localVal,       \* Local value variable per process
    localAddr,      \* Local address variable per process
    localNode,      \* Local node record per process
    localLeft,      \* Local left pointer per process
    localRight,     \* Local right pointer per process
    localResult,    \* Local result per process (for pop operations)
    valBag,         \* Multiset of values currently in the deque
    op              \* Current operation type per process

vars == <<mem, leftHat, rightHat, freelist, pc, localVal, localAddr, 
          localNode, localLeft, localRight, localResult, valBag, op>>

\* Node record structure: [val: Values, left: Addresses \cup {NullAddr}, right: Addresses \cup {NullAddr}]
NullNode == [val |-> CHOOSE v \in Values : TRUE, left |-> NullAddr, right |-> NullAddr]

\* Control locations
\* T1: Test idle/choosing operation
\* PL1-PL5: pushLeft states
\* PR1-PR5: pushRight states
\* POL1-POL6: popLeft states
\* POR1-POR6: popRight states

ControlLocations == {"T1", "PL1", "PL2", "PL3", "PL4", "PL5",
                     "PR1", "PR2", "PR3", "PR4", "PR5",
                     "POL1", "POL2", "POL3", "POL4", "POL5", "POL6",
                     "POR1", "POR2", "POR3", "POR4", "POR5", "POR6"}

Operations == {"none", "pushLeft", "pushRight", "popLeft", "popRight"}

TypeInvariant ==
    /\ mem \in [Addresses -> [val: Values, left: Addresses \cup {NullAddr}, right: Addresses \cup {NullAddr}]]
    /\ leftHat \in Addresses \cup {NullAddr}
    /\ rightHat \in Addresses \cup {NullAddr}
    /\ freelist \subseteq Addresses
    /\ pc \in [Procs -> ControlLocations]
    /\ localVal \in [Procs -> Values]
    /\ localAddr \in [Procs -> Addresses \cup {NullAddr}]
    /\ localNode \in [Procs -> [val: Values, left: Addresses \cup {NullAddr}, right: Addresses \cup {NullAddr}]]
    /\ localLeft \in [Procs -> Addresses \cup {NullAddr}]
    /\ localRight \in [Procs -> Addresses \cup {NullAddr}]
    /\ localResult \in [Procs -> Values \cup {NullAddr}]
    /\ op \in [Procs -> Operations]

\* Helper: Add value to bag
AddToBag(bag, v) == 
    IF v \in DOMAIN bag THEN [bag EXCEPT ![v] = @ + 1]
    ELSE bag @@ (v :> 1)

\* Helper: Remove value from bag  
RemoveFromBag(bag, v) ==
    IF v \in DOMAIN bag THEN
        IF bag[v] = 1 THEN [x \in (DOMAIN bag \ {v}) |-> bag[x]]
        ELSE [bag EXCEPT ![v] = @ - 1]
    ELSE bag

\* Initialize empty bag
EmptyBag == [v \in {} |-> 0]

Init ==
    /\ mem = [a \in Addresses |-> [val |-> CHOOSE v \in Values : TRUE, left |-> NullAddr, right |-> NullAddr]]
    /\ leftHat = NullAddr
    /\ rightHat = NullAddr
    /\ freelist = Addresses
    /\ pc = [p \in Procs |-> "T1"]
    /\ localVal = [p \in Procs |-> CHOOSE v \in Values : TRUE]
    /\ localAddr = [p \in Procs |-> NullAddr]
    /\ localNode = [p \in Procs |-> NullNode]
    /\ localLeft = [p \in Procs |-> NullAddr]
    /\ localRight = [p \in Procs |-> NullAddr]
    /\ localResult = [p \in Procs |-> NullAddr]
    /\ valBag = EmptyBag
    /\ op = [p \in Procs |-> "none"]

\* Test process: Choose operation nondeterministically
TestChoose(p) ==
    /\ pc[p] = "T1"
    /\ \E o \in {"pushLeft", "pushRight", "popLeft", "popRight"} :
        /\ op' = [op EXCEPT ![p] = o]
        /\ CASE o = "pushLeft" -> 
                /\ \E v \in Values : localVal' = [localVal EXCEPT ![p] = v]
                /\ pc' = [pc EXCEPT ![p] = "PL1"]
           [] o = "pushRight" ->
                /\ \E v \in Values : localVal' = [localVal EXCEPT ![p] = v]
                /\ pc' = [pc EXCEPT ![p] = "PR1"]
           [] o = "popLeft" ->
                /\ localVal' = localVal
                /\ pc' = [pc EXCEPT ![p] = "POL1"]
           [] o = "popRight" ->
                /\ localVal' = localVal
                /\ pc' = [pc EXCEPT ![p] = "POR1"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localAddr, localNode, 
                   localLeft, localRight, localResult, valBag>>

\* PushLeft operations
PushLeft1(p) == \* Allocate node
    /\ pc[p] = "PL1"
    /\ freelist # {}
    /\ \E a \in freelist :
        /\ localAddr' = [localAddr EXCEPT ![p] = a]
        /\ freelist' = freelist \ {a}
        /\ pc' = [pc EXCEPT ![p] = "PL2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, localVal, localNode, localLeft, 
                   localRight, localResult, valBag, op>>

PushLeft2(p) == \* Read leftHat
    /\ pc[p] = "PL2"
    /\ localLeft' = [localLeft EXCEPT ![p] = leftHat]
    /\ pc' = [pc EXCEPT ![p] = "PL3"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localRight, localResult, valBag, op>>

PushLeft3(p) == \* Prepare node
    /\ pc[p] = "PL3"
    /\ localNode' = [localNode EXCEPT ![p] = [val |-> localVal[p], left |-> NullAddr, right |-> localLeft[p]]]
    /\ pc' = [pc EXCEPT ![p] = "PL4"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localLeft, localRight, localResult, valBag, op>>

PushLeft4(p) == \* DCAS-like: update leftHat and possibly link previous node
    /\ pc[p] = "PL4"
    /\ IF localLeft[p] = NullAddr
       THEN \* Empty deque case
            IF leftHat = NullAddr /\ rightHat = NullAddr
            THEN /\ mem' = [mem EXCEPT ![localAddr[p]] = localNode[p]]
                 /\ leftHat' = localAddr[p]
                 /\ rightHat' = localAddr[p]
                 /\ valBag' = AddToBag(valBag, localVal[p])
                 /\ pc' = [pc EXCEPT ![p] = "PL5"]
            ELSE \* Retry - state changed
                 /\ pc' = [pc EXCEPT ![p] = "PL2"]
                 /\ UNCHANGED <<mem, leftHat, rightHat, valBag>>
       ELSE \* Non-empty deque case - DCAS on leftHat and previous node's left pointer
            IF leftHat = localLeft[p] /\ mem[localLeft[p]].left = NullAddr
            THEN /\ mem' = [mem EXCEPT ![localAddr[p]] = localNode[p],
                                       ![localLeft[p]].left = localAddr[p]]
                 /\ leftHat' = localAddr[p]
                 /\ valBag' = AddToBag(valBag, localVal[p])
                 /\ pc' = [pc EXCEPT ![p] = "PL5"]
                 /\ UNCHANGED rightHat
            ELSE \* Retry - state changed
                 /\ pc' = [pc EXCEPT ![p] = "PL2"]
                 /\ UNCHANGED <<mem, leftHat, rightHat, valBag>>
    /\ UNCHANGED <<freelist, localVal, localAddr, localNode, localLeft, 
                   localRight, localResult, op>>

PushLeft5(p) == \* Return to T1
    /\ pc[p] = "PL5"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ op' = [op EXCEPT ![p] = "none"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localLeft, localRight, localResult, valBag>>

\* PushRight operations (symmetric to PushLeft)
PushRight1(p) ==
    /\ pc[p] = "PR1"
    /\ freelist # {}
    /\ \E a \in freelist :
        /\ localAddr' = [localAddr EXCEPT ![p] = a]
        /\ freelist' = freelist \ {a}
        /\ pc' = [pc EXCEPT ![p] = "PR2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, localVal, localNode, localLeft, 
                   localRight, localResult, valBag, op>>

PushRight2(p) ==
    /\ pc[p] = "PR2"
    /\ localRight' = [localRight EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PR3"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localLeft, localResult, valBag, op>>

PushRight3(p) ==
    /\ pc[p] = "PR3"
    /\ localNode' = [localNode EXCEPT ![p] = [val |-> localVal[p], left |-> localRight[p], right |-> NullAddr]]
    /\ pc' = [pc EXCEPT ![p] = "PR4"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localLeft, localRight, localResult, valBag, op>>

PushRight4(p) ==
    /\ pc[p] = "PR4"
    /\ IF localRight[p] = NullAddr
       THEN
            IF leftHat = NullAddr /\ rightHat = NullAddr
            THEN /\ mem' = [mem EXCEPT ![localAddr[p]] = localNode[p]]
                 /\ leftHat' = localAddr[p]
                 /\ rightHat' = localAddr[p]
                 /\ valBag' = AddToBag(valBag, localVal[p])
                 /\ pc' = [pc EXCEPT ![p] = "PR5"]
            ELSE /\ pc' = [pc EXCEPT ![p] = "PR2"]
                 /\ UNCHANGED <<mem, leftHat, rightHat, valBag>>
       ELSE
            IF rightHat = localRight[p] /\ mem[localRight[p]].right = NullAddr
            THEN /\ mem' = [mem EXCEPT ![localAddr[p]] = localNode[p],
                                       ![localRight[p]].right = localAddr[p]]
                 /\ rightHat' = localAddr[p]
                 /\ valBag' = AddToBag(valBag, localVal[p])
                 /\ pc' = [pc EXCEPT ![p] = "PR5"]
                 /\ UNCHANGED leftHat
            ELSE /\ pc' = [pc EXCEPT ![p] = "PR2"]
                 /\ UNCHANGED <<mem, leftHat, rightHat, valBag>>
    /\ UNCHANGED <<freelist, localVal, localAddr, localNode, localLeft, 
                   localRight, localResult, op>>

PushRight5(p) ==
    /\ pc[p] = "PR5"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ op' = [op EXCEPT ![p] = "none"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localLeft, localRight, localResult, valBag>>

\* PopLeft operations
PopLeft1(p) == \* Read leftHat
    /\ pc[p] = "POL1"
    /\ localLeft' = [localLeft EXCEPT ![p] = leftHat]
    /\ pc' = [pc EXCEPT ![p] = "POL2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localRight, localResult, valBag, op>>

PopLeft2(p) == \* Check if empty
    /\ pc[p] = "POL2"
    /\ IF localLeft[p] = NullAddr
       THEN /\ localResult' = [localResult EXCEPT ![p] = NullAddr]
            /\ pc' = [pc EXCEPT ![p] = "POL6"]
       ELSE /\ localNode' = [localNode EXCEPT ![p] = mem[localLeft[p]]]
            /\ pc' = [pc EXCEPT ![p] = "POL3"]
            /\ UNCHANGED localResult
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localLeft, localRight, valBag, op>>
    /\ IF localLeft[p] = NullAddr THEN UNCHANGED localNode ELSE TRUE

PopLeft3(p) == \* Read right neighbor
    /\ pc[p] = "POL3"
    /\ localRight' = [localRight EXCEPT ![p] = localNode[p].right]
    /\ pc' = [pc EXCEPT ![p] = "POL4"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localLeft, localResult, valBag, op>>

PopLeft4(p) == \* DCAS-like removal
    /\ pc[p] = "POL4"
    /\ IF localRight[p] = NullAddr
       THEN \* Single element case
            IF leftHat = localLeft[p] /\ rightHat = localLeft[p]
            THEN /\ leftHat' = NullAddr
                 /\ rightHat' = NullAddr
                 /\ localResult' = [localResult EXCEPT ![p] = localNode[p].val]
                 /\ valBag' = RemoveFromBag(valBag, localNode[p].val)
                 /\ freelist' = freelist \cup {localLeft[p]}
                 /\ pc' = [pc EXCEPT ![p] = "POL5"]
                 /\ UNCHANGED mem
            ELSE /\ pc' = [pc EXCEPT ![p] = "POL1"]
                 /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localResult, valBag>>
       ELSE \* Multiple elements
            IF leftHat = localLeft[p] /\ mem[localRight[p]].left = localLeft[p]
            THEN /\ mem' = [mem EXCEPT ![localRight[p]].left = NullAddr]
                 /\ leftHat' = localRight[p]
                 /\ localResult' = [localResult EXCEPT ![p] = localNode[p].val]
                 /\ valBag' = RemoveFromBag(valBag, localNode[p].val)
                 /\ freelist' = freelist \cup {localLeft[p]}
                 /\ pc' = [pc EXCEPT ![p] = "POL5"]
                 /\ UNCHANGED rightHat
            ELSE /\ pc' = [pc EXCEPT ![p] = "POL1"]
                 /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localResult, valBag>>
    /\ UNCHANGED <<localVal, localAddr, localNode, localLeft, localRight, op>>

PopLeft5(p) == \* Success return
    /\ pc[p] = "POL5"
    /\ pc' = [pc EXCEPT ![p] = "POL6"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localLeft, localRight, localResult, valBag, op>>

PopLeft6(p) == \* Return to T1
    /\ pc[p] = "POL6"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ op' = [op EXCEPT ![p] = "none"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localLeft, localRight, localResult, valBag>>

\* PopRight operations (symmetric to PopLeft)
PopRight1(p) ==
    /\ pc[p] = "POR1"
    /\ localRight' = [localRight EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "POR2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localLeft, localResult, valBag, op>>

PopRight2(p) ==
    /\ pc[p] = "POR2"
    /\ IF localRight[p] = NullAddr
       THEN /\ localResult' = [localResult EXCEPT ![p] = NullAddr]
            /\ pc' = [pc EXCEPT ![p] = "POR6"]
            /\ UNCHANGED localNode
       ELSE /\ localNode' = [localNode EXCEPT ![p] = mem[localRight[p]]]
            /\ pc' = [pc EXCEPT ![p] = "POR3"]
            /\ UNCHANGED localResult
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localLeft, localRight, valBag, op>>

PopRight3(p) ==
    /\ pc[p] = "POR3"
    /\ localLeft' = [localLeft EXCEPT ![p] = localNode[p].left]
    /\ pc' = [pc EXCEPT ![p] = "POR4"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localRight, localResult, valBag, op>>

PopRight4(p) ==
    /\ pc[p] = "POR4"
    /\ IF localLeft[p] = NullAddr
       THEN
            IF leftHat = localRight[p] /\ rightHat = localRight[p]
            THEN /\ leftHat' = NullAddr
                 /\ rightHat' = NullAddr
                 /\ localResult' = [localResult EXCEPT ![p] = localNode[p].val]
                 /\ valBag' = RemoveFromBag(valBag, localNode[p].val)
                 /\ freelist' = freelist \cup {localRight[p]}
                 /\ pc' = [pc EXCEPT ![p] = "POR5"]
                 /\ UNCHANGED mem
            ELSE /\ pc' = [pc EXCEPT ![p] = "POR1"]
                 /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localResult, valBag>>
       ELSE
            IF rightHat = localRight[p] /\ mem[localLeft[p]].right = localRight[p]
            THEN /\ mem' = [mem EXCEPT ![localLeft[p]].right = NullAddr]
                 /\ rightHat' = localLeft[p]
                 /\ localResult' = [localResult EXCEPT ![p] = localNode[p].val]
                 /\ valBag' = RemoveFromBag(valBag, localNode[p].val)
                 /\ freelist' = freelist \cup {localRight[p]}
                 /\ pc' = [pc EXCEPT ![p] = "POR5"]
                 /\ UNCHANGED leftHat
            ELSE /\ pc' = [pc EXCEPT ![p] = "POR1"]
                 /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localResult, valBag>>
    /\ UNCHANGED <<localVal, localAddr, localNode, localLeft, localRight, op>>

PopRight5(p) ==
    /\ pc[p] = "POR5"
    /\ pc' = [pc EXCEPT ![p] = "POR6"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localLeft, localRight, localResult, valBag, op>>

PopRight6(p) ==
    /\ pc[p] = "POR6"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ op' = [op EXCEPT ![p] = "none"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localVal, localAddr, 
                   localNode, localLeft, localRight, localResult, valBag>>

\* Next state relation
Next ==
    \E p \in Procs :
        \/ TestChoose(p)
        \/ PushLeft1(p) \/ PushLeft2(p) \/ PushLeft3(p) \/ PushLeft4(p) \/ PushLeft5(p)
        \/ PushRight1(p) \/ PushRight2(p) \/ PushRight3(p) \/ PushRight4(p) \/ PushRight5(p)
        \/ PopLeft1(p) \/ PopLeft2(p) \/ PopLeft3(p) \/ PopLeft4(p) \/ PopLeft5(p) \/ PopLeft6(p)
        \/ PopRight1(p) \/ PopRight2(p) \/ PopRight3(p) \/ PopRight4(p) \/ PopRight5(p) \/ PopRight6(p)

\* Fairness: weak fairness for all process actions
Fairness ==
    \A p \in Procs :
        /\ WF_vars(TestChoose(p))
        /\ WF_vars(PushLeft1(p)) /\ WF_vars(PushLeft2(p)) /\ WF_vars(PushLeft3(p)) 
        /\ WF_vars(PushLeft4(p)) /\ WF_vars(PushLeft5(p))
        /\ WF_vars(PushRight1(p)) /\ WF_vars(PushRight2(p)) /\ WF_vars(PushRight3(p))
        /\ WF_vars(PushRight4(p)) /\ WF_vars(PushRight5(p))
        /\ WF_vars(PopLeft1(p)) /\ WF_vars(PopLeft2(p)) /\ WF_vars(PopLeft3(p))
        /\ WF_vars(PopLeft4(p)) /\ WF_vars(PopLeft5(p)) /\ WF_vars(PopLeft6(p))
        /\ WF_vars(PopRight1(p)) /\ WF_vars(PopRight2(p)) /\ WF_vars(PopRight3(p))
        /\ WF_vars(PopRight4(p)) /\ WF_vars(PopRight5(p)) /\ WF_vars(PopRight6(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: valBag counts are never negative
ValBagNonNegative ==
    \A v \in DOMAIN valBag : valBag[v] >= 0

\* Safety: deque pointers are consistent (if one is null, both are null when deque is truly empty)
DequeConsistency ==
    (leftHat = NullAddr) <=> (rightHat = NullAddr)

\* Liveness: every test process returns to T1 infinitely often
LivenessT1 == \A p \in Procs : []<>(pc[p] = "T1")

================================================================================