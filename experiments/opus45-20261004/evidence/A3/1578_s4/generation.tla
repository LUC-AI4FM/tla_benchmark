---------------------------- MODULE ConcurrentDeque ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Procs,          \* Set of process IDs
    Addresses,      \* Set of memory addresses
    Values,         \* Set of values that can be stored
    NullAddr        \* Null address constant

VARIABLES
    mem,            \* Memory: mapping from addresses to node records
    leftHat,        \* Left hat pointer (head of deque from left)
    rightHat,       \* Right hat pointer (head of deque from right)
    freelist,       \* Set of free addresses for allocation
    pc,             \* Program counter for each process
    localNode,      \* Local node pointer per process
    localVal,       \* Local value per process
    localLeft,      \* Local left pointer per process
    localRight,     \* Local right pointer per process
    localResult,    \* Local result per process (for pop operations)
    valBag,         \* Multiset of values in the deque (for consistency check)
    opType          \* Current operation type per process

vars == <<mem, leftHat, rightHat, freelist, pc, localNode, localVal, 
          localLeft, localRight, localResult, valBag, opType>>

\* Node record structure: [val: Value, left: Address, right: Address]
NullNode == [val |-> CHOOSE v \in Values : TRUE, left |-> NullAddr, right |-> NullAddr]

\* Helper: Add to bag
AddToBag(bag, v) == 
    IF v \in DOMAIN bag THEN [bag EXCEPT ![v] = @ + 1]
    ELSE bag @@ (v :> 1)

\* Helper: Remove from bag  
RemoveFromBag(bag, v) ==
    IF v \in DOMAIN bag THEN
        IF bag[v] = 1 THEN [x \in (DOMAIN bag \ {v}) |-> bag[x]]
        ELSE [bag EXCEPT ![v] = @ - 1]
    ELSE bag

\* Helper: Check if bag contains value
BagContains(bag, v) == v \in DOMAIN bag /\ bag[v] > 0

\* Initialize specification
Init ==
    /\ mem = [a \in Addresses |-> NullNode]
    /\ leftHat = NullAddr
    /\ rightHat = NullAddr
    /\ freelist = Addresses
    /\ pc = [p \in Procs |-> "T1"]
    /\ localNode = [p \in Procs |-> NullAddr]
    /\ localVal = [p \in Procs |-> CHOOSE v \in Values : TRUE]
    /\ localLeft = [p \in Procs |-> NullAddr]
    /\ localRight = [p \in Procs |-> NullAddr]
    /\ localResult = [p \in Procs |-> CHOOSE v \in Values : TRUE]
    /\ valBag = [v \in {} |-> 0]
    /\ opType = [p \in Procs |-> "none"]

\* Test process chooses operation at T1
ChooseOp(p) ==
    /\ pc[p] = "T1"
    /\ \E op \in {"pushLeft", "pushRight", "popLeft", "popRight"} :
        /\ opType' = [opType EXCEPT ![p] = op]
        /\ IF op \in {"pushLeft", "pushRight"} 
           THEN /\ \E v \in Values : localVal' = [localVal EXCEPT ![p] = v]
                /\ pc' = [pc EXCEPT ![p] = "Alloc"]
           ELSE /\ localVal' = localVal
                /\ pc' = [pc EXCEPT ![p] = IF op = "popLeft" THEN "PL1" ELSE "PR1"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localLeft, localRight, localResult, valBag>>

\* Allocate node for push operations
Allocate(p) ==
    /\ pc[p] = "Alloc"
    /\ freelist # {}
    /\ \E addr \in freelist :
        /\ localNode' = [localNode EXCEPT ![p] = addr]
        /\ freelist' = freelist \ {addr}
        /\ mem' = [mem EXCEPT ![addr] = [val |-> localVal[p], left |-> NullAddr, right |-> NullAddr]]
        /\ pc' = [pc EXCEPT ![p] = IF opType[p] = "pushLeft" THEN "PSL1" ELSE "PSR1"]
    /\ UNCHANGED <<leftHat, rightHat, localVal, localLeft, localRight, localResult, valBag, opType>>

\* PushLeft Step 1: Read leftHat
PushLeftStep1(p) ==
    /\ pc[p] = "PSL1"
    /\ localLeft' = [localLeft EXCEPT ![p] = leftHat]
    /\ pc' = [pc EXCEPT ![p] = "PSL2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localVal, localRight, localResult, valBag, opType>>

\* PushLeft Step 2: Check if empty and handle
PushLeftStep2(p) ==
    /\ pc[p] = "PSL2"
    /\ IF localLeft[p] = NullAddr
       THEN \* Empty deque - try DCAS to set both hats
            /\ IF leftHat = NullAddr /\ rightHat = NullAddr
               THEN /\ leftHat' = localNode[p]
                    /\ rightHat' = localNode[p]
                    /\ valBag' = AddToBag(valBag, localVal[p])
                    /\ pc' = [pc EXCEPT ![p] = "T1"]
               ELSE /\ pc' = [pc EXCEPT ![p] = "PSL1"]  \* Retry
                    /\ UNCHANGED <<leftHat, rightHat, valBag>>
            /\ UNCHANGED <<mem>>
       ELSE \* Non-empty - set node's right pointer
            /\ mem' = [mem EXCEPT ![localNode[p]].right = localLeft[p]]
            /\ pc' = [pc EXCEPT ![p] = "PSL3"]
            /\ UNCHANGED <<leftHat, rightHat, valBag>>
    /\ UNCHANGED <<freelist, localNode, localVal, localLeft, localRight, localResult, opType>>

\* PushLeft Step 3: DCAS to update leftHat and prev node's left pointer
PushLeftStep3(p) ==
    /\ pc[p] = "PSL3"
    /\ IF leftHat = localLeft[p] /\ localLeft[p] # NullAddr /\ mem[localLeft[p]].left = NullAddr
       THEN /\ leftHat' = localNode[p]
            /\ mem' = [mem EXCEPT ![localLeft[p]].left = localNode[p]]
            /\ valBag' = AddToBag(valBag, localVal[p])
            /\ pc' = [pc EXCEPT ![p] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "PSL1"]  \* Retry
            /\ UNCHANGED <<leftHat, mem, valBag>>
    /\ UNCHANGED <<rightHat, freelist, localNode, localVal, localLeft, localRight, localResult, opType>>

\* PushRight Step 1: Read rightHat
PushRightStep1(p) ==
    /\ pc[p] = "PSR1"
    /\ localRight' = [localRight EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PSR2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localVal, localLeft, localResult, valBag, opType>>

\* PushRight Step 2: Check if empty and handle
PushRightStep2(p) ==
    /\ pc[p] = "PSR2"
    /\ IF localRight[p] = NullAddr
       THEN \* Empty deque - try DCAS to set both hats
            /\ IF leftHat = NullAddr /\ rightHat = NullAddr
               THEN /\ leftHat' = localNode[p]
                    /\ rightHat' = localNode[p]
                    /\ valBag' = AddToBag(valBag, localVal[p])
                    /\ pc' = [pc EXCEPT ![p] = "T1"]
               ELSE /\ pc' = [pc EXCEPT ![p] = "PSR1"]  \* Retry
                    /\ UNCHANGED <<leftHat, rightHat, valBag>>
            /\ UNCHANGED <<mem>>
       ELSE \* Non-empty - set node's left pointer
            /\ mem' = [mem EXCEPT ![localNode[p]].left = localRight[p]]
            /\ pc' = [pc EXCEPT ![p] = "PSR3"]
            /\ UNCHANGED <<leftHat, rightHat, valBag>>
    /\ UNCHANGED <<freelist, localNode, localVal, localLeft, localRight, localResult, opType>>

\* PushRight Step 3: DCAS to update rightHat and prev node's right pointer
PushRightStep3(p) ==
    /\ pc[p] = "PSR3"
    /\ IF rightHat = localRight[p] /\ localRight[p] # NullAddr /\ mem[localRight[p]].right = NullAddr
       THEN /\ rightHat' = localNode[p]
            /\ mem' = [mem EXCEPT ![localRight[p]].right = localNode[p]]
            /\ valBag' = AddToBag(valBag, localVal[p])
            /\ pc' = [pc EXCEPT ![p] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "PSR1"]  \* Retry
            /\ UNCHANGED <<rightHat, mem, valBag>>
    /\ UNCHANGED <<leftHat, freelist, localNode, localVal, localLeft, localRight, localResult, opType>>

\* PopLeft Step 1: Read leftHat
PopLeftStep1(p) ==
    /\ pc[p] = "PL1"
    /\ localLeft' = [localLeft EXCEPT ![p] = leftHat]
    /\ pc' = [pc EXCEPT ![p] = "PL2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localVal, localRight, localResult, valBag, opType>>

\* PopLeft Step 2: Check if empty or single element
PopLeftStep2(p) ==
    /\ pc[p] = "PL2"
    /\ IF localLeft[p] = NullAddr
       THEN \* Empty - return
            /\ pc' = [pc EXCEPT ![p] = "T1"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localVal, localLeft, localRight, localResult, valBag>>
       ELSE /\ localRight' = [localRight EXCEPT ![p] = mem[localLeft[p]].right]
            /\ localResult' = [localResult EXCEPT ![p] = mem[localLeft[p]].val]
            /\ pc' = [pc EXCEPT ![p] = "PL3"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localVal, localLeft, valBag>>
    /\ UNCHANGED <<opType>>

\* PopLeft Step 3: Try to remove
PopLeftStep3(p) ==
    /\ pc[p] = "PL3"
    /\ IF localRight[p] = NullAddr
       THEN \* Single element - DCAS both hats to null
            /\ IF leftHat = localLeft[p] /\ rightHat = localLeft[p]
               THEN /\ leftHat' = NullAddr
                    /\ rightHat' = NullAddr
                    /\ freelist' = freelist \cup {localLeft[p]}
                    /\ valBag' = RemoveFromBag(valBag, localResult[p])
                    /\ pc' = [pc EXCEPT ![p] = "T1"]
               ELSE /\ pc' = [pc EXCEPT ![p] = "PL1"]  \* Retry
                    /\ UNCHANGED <<leftHat, rightHat, freelist, valBag>>
            /\ UNCHANGED <<mem>>
       ELSE \* Multiple elements - DCAS leftHat and neighbor's left ptr
            /\ IF leftHat = localLeft[p] /\ mem[localRight[p]].left = localLeft[p]
               THEN /\ leftHat' = localRight[p]
                    /\ mem' = [mem EXCEPT ![localRight[p]].left = NullAddr]
                    /\ freelist' = freelist \cup {localLeft[p]}
                    /\ valBag' = RemoveFromBag(valBag, localResult[p])
                    /\ pc' = [pc EXCEPT ![p] = "T1"]
               ELSE /\ pc' = [pc EXCEPT ![p] = "PL1"]  \* Retry
                    /\ UNCHANGED <<leftHat, mem, freelist, valBag>>
            /\ UNCHANGED <<rightHat>>
    /\ UNCHANGED <<localNode, localVal, localLeft, localRight, localResult, opType>>

\* PopRight Step 1: Read rightHat
PopRightStep1(p) ==
    /\ pc[p] = "PR1"
    /\ localRight' = [localRight EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PR2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localVal, localLeft, localResult, valBag, opType>>

\* PopRight Step 2: Check if empty or single element
PopRightStep2(p) ==
    /\ pc[p] = "PR2"
    /\ IF localRight[p] = NullAddr
       THEN \* Empty - return
            /\ pc' = [pc EXCEPT ![p] = "T1"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localVal, localLeft, localRight, localResult, valBag>>
       ELSE /\ localLeft' = [localLeft EXCEPT ![p] = mem[localRight[p]].left]
            /\ localResult' = [localResult EXCEPT ![p] = mem[localRight[p]].val]
            /\ pc' = [pc EXCEPT ![p] = "PR3"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localVal, localRight, valBag>>
    /\ UNCHANGED <<opType>>

\* PopRight Step 3: Try to remove
PopRightStep3(p) ==
    /\ pc[p] = "PR3"
    /\ IF localLeft[p] = NullAddr
       THEN \* Single element - DCAS both hats to null
            /\ IF leftHat = localRight[p] /\ rightHat = localRight[p]
               THEN /\ leftHat' = NullAddr
                    /\ rightHat' = NullAddr
                    /\ freelist' = freelist \cup {localRight[p]}
                    /\ valBag' = RemoveFromBag(valBag, localResult[p])
                    /\ pc' = [pc EXCEPT ![p] = "T1"]
               ELSE /\ pc' = [pc EXCEPT ![p] = "PR1"]  \* Retry
                    /\ UNCHANGED <<leftHat, rightHat, freelist, valBag>>
            /\ UNCHANGED <<mem>>
       ELSE \* Multiple elements - DCAS rightHat and neighbor's right ptr
            /\ IF rightHat = localRight[p] /\ mem[localLeft[p]].right = localRight[p]
               THEN /\ rightHat' = localLeft[p]
                    /\ mem' = [mem EXCEPT ![localLeft[p]].right = NullAddr]
                    /\ freelist' = freelist \cup {localRight[p]}
                    /\ valBag' = RemoveFromBag(valBag, localResult[p])
                    /\ pc' = [pc EXCEPT ![p] = "T1"]
               ELSE /\ pc' = [pc EXCEPT ![p] = "PR1"]  \* Retry
                    /\ UNCHANGED <<rightHat, mem, freelist, valBag>>
            /\ UNCHANGED <<leftHat>>
    /\ UNCHANGED <<localNode, localVal, localLeft, localRight, localResult, opType>>

\* Next state relation
Next ==
    \E p \in Procs :
        \/ ChooseOp(p)
        \/ Allocate(p)
        \/ PushLeftStep1(p)
        \/ PushLeftStep2(p)
        \/ PushLeftStep3(p)
        \/ PushRightStep1(p)
        \/ PushRightStep2(p)
        \/ PushRightStep3(p)
        \/ PopLeftStep1(p)
        \/ PopLeftStep2(p)
        \/ PopLeftStep3(p)
        \/ PopRightStep1(p)
        \/ PopRightStep2(p)
        \/ PopRightStep3(p)

\* Fairness: weak fairness for all process actions
Fairness == 
    \A p \in Procs :
        /\ WF_vars(ChooseOp(p))
        /\ WF_vars(Allocate(p))
        /\ WF_vars(PushLeftStep1(p))
        /\ WF_vars(PushLeftStep2(p))
        /\ WF_vars(PushLeftStep3(p))
        /\ WF_vars(PushRightStep1(p))
        /\ WF_vars(PushRightStep2(p))
        /\ WF_vars(PushRightStep3(p))
        /\ WF_vars(PopLeftStep1(p))
        /\ WF_vars(PopLeftStep2(p))
        /\ WF_vars(PopLeftStep3(p))
        /\ WF_vars(PopRightStep1(p))
        /\ WF_vars(PopRightStep2(p))
        /\ WF_vars(PopRightStep3(p))

\* Specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: ValBag consistency - values are non-negative
ValBagConsistency == \A v \in DOMAIN valBag : valBag[v] >= 0

\* Safety: Hat consistency - both null or both non-null
HatConsistency == (leftHat = NullAddr) <=> (rightHat = NullAddr)

\* Safety: Type invariant
TypeInvariant ==
    /\ leftHat \in Addresses \cup {NullAddr}
    /\ rightHat \in Addresses \cup {NullAddr}
    /\ freelist \subseteq Addresses
    /\ \A p \in Procs : pc[p] \in {"T1", "Alloc", "PSL1", "PSL2", "PSL3", 
                                   "PSR1", "PSR2", "PSR3", "PL1", "PL2", "PL3",
                                   "PR1", "PR2", "PR3"}

\* Liveness: Every test process returns to T1 infinitely often
LivenessT1 == \A p \in Procs : []<>(pc[p] = "T1")

================================================================================