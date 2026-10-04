---------------------------- MODULE ConcurrentDeque ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    Procs,          \* Set of process identifiers
    Addresses,      \* Set of memory addresses
    Values,         \* Set of values that can be stored
    NullAddr        \* Null address constant

VARIABLES
    mem,            \* Memory: mapping from addresses to node records
    leftHat,        \* Left hat pointer (left end of deque)
    rightHat,       \* Right hat pointer (right end of deque)
    freelist,       \* Set of free addresses for allocation
    pc,             \* Program counter for each process
    op,             \* Current operation type for each process
    arg,            \* Argument (value) for push operations
    result,         \* Result of pop operations
    localNode,      \* Local node pointer for each process
    localLeft,      \* Local copy of left pointer
    localRight,     \* Local copy of right pointer
    newNode,        \* Newly allocated node
    oldLeft,        \* Snapshot of leftHat for CAS
    oldRight,       \* Snapshot of rightHat for CAS
    valBag          \* Multiset tracking values in the deque

vars == <<mem, leftHat, rightHat, freelist, pc, op, arg, result, 
          localNode, localLeft, localRight, newNode, oldLeft, oldRight, valBag>>

\* Node record structure: [val: Value, left: Address, right: Address]
NullNode == [val |-> CHOOSE v \in Values : TRUE, left |-> NullAddr, right |-> NullAddr]

\* Program counter locations
PCLocations == {"T1", "PushL1", "PushL2", "PushL3", "PushL4", "PushL5",
                "PushR1", "PushR2", "PushR3", "PushR4", "PushR5",
                "PopL1", "PopL2", "PopL3", "PopL4", "PopL5",
                "PopR1", "PopR2", "PopR3", "PopR4", "PopR5",
                "Done"}

TypeOK ==
    /\ mem \in [Addresses -> [val: Values, left: Addresses \cup {NullAddr}, right: Addresses \cup {NullAddr}]]
    /\ leftHat \in Addresses \cup {NullAddr}
    /\ rightHat \in Addresses \cup {NullAddr}
    /\ freelist \subseteq Addresses
    /\ pc \in [Procs -> PCLocations]
    /\ op \in [Procs -> {"none", "pushLeft", "pushRight", "popLeft", "popRight"}]
    /\ arg \in [Procs -> Values \cup {NullAddr}]
    /\ result \in [Procs -> Values \cup {NullAddr}]
    /\ localNode \in [Procs -> Addresses \cup {NullAddr}]
    /\ localLeft \in [Procs -> Addresses \cup {NullAddr}]
    /\ localRight \in [Procs -> Addresses \cup {NullAddr}]
    /\ newNode \in [Procs -> Addresses \cup {NullAddr}]
    /\ oldLeft \in [Procs -> Addresses \cup {NullAddr}]
    /\ oldRight \in [Procs -> Addresses \cup {NullAddr}]

\* Initialize the specification
Init ==
    /\ mem = [a \in Addresses |-> [val |-> CHOOSE v \in Values : TRUE, left |-> NullAddr, right |-> NullAddr]]
    /\ leftHat = NullAddr
    /\ rightHat = NullAddr
    /\ freelist = Addresses
    /\ pc = [p \in Procs |-> "T1"]
    /\ op = [p \in Procs |-> "none"]
    /\ arg = [p \in Procs |-> NullAddr]
    /\ result = [p \in Procs |-> NullAddr]
    /\ localNode = [p \in Procs |-> NullAddr]
    /\ localLeft = [p \in Procs |-> NullAddr]
    /\ localRight = [p \in Procs |-> NullAddr]
    /\ newNode = [p \in Procs |-> NullAddr]
    /\ oldLeft = [p \in Procs |-> NullAddr]
    /\ oldRight = [p \in Procs |-> NullAddr]
    /\ valBag = [v \in Values |-> 0]

\* Test process: nondeterministically choose an operation
TestChoose(p) ==
    /\ pc[p] = "T1"
    /\ \/ /\ freelist /= {}
          /\ \E v \in Values:
              /\ op' = [op EXCEPT ![p] = "pushLeft"]
              /\ arg' = [arg EXCEPT ![p] = v]
              /\ pc' = [pc EXCEPT ![p] = "PushL1"]
       \/ /\ freelist /= {}
          /\ \E v \in Values:
              /\ op' = [op EXCEPT ![p] = "pushRight"]
              /\ arg' = [arg EXCEPT ![p] = v]
              /\ pc' = [pc EXCEPT ![p] = "PushR1"]
       \/ /\ op' = [op EXCEPT ![p] = "popLeft"]
          /\ arg' = arg
          /\ pc' = [pc EXCEPT ![p] = "PopL1"]
       \/ /\ op' = [op EXCEPT ![p] = "popRight"]
          /\ arg' = arg
          /\ pc' = [pc EXCEPT ![p] = "PopR1"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, result, localNode, 
                   localLeft, localRight, newNode, oldLeft, oldRight, valBag>>

\* PushLeft operation steps
PushL1(p) ==
    /\ pc[p] = "PushL1"
    /\ freelist /= {}
    /\ \E a \in freelist:
        /\ newNode' = [newNode EXCEPT ![p] = a]
        /\ freelist' = freelist \ {a}
        /\ mem' = [mem EXCEPT ![a] = [val |-> arg[p], left |-> NullAddr, right |-> NullAddr]]
    /\ pc' = [pc EXCEPT ![p] = "PushL2"]
    /\ UNCHANGED <<leftHat, rightHat, op, arg, result, localNode, localLeft, localRight, oldLeft, oldRight, valBag>>

PushL2(p) ==
    /\ pc[p] = "PushL2"
    /\ oldLeft' = [oldLeft EXCEPT ![p] = leftHat]
    /\ oldRight' = [oldRight EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PushL3"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, op, arg, result, localNode, localLeft, localRight, newNode, valBag>>

PushL3(p) ==
    /\ pc[p] = "PushL3"
    /\ mem' = [mem EXCEPT ![newNode[p]].right = oldLeft[p]]
    /\ pc' = [pc EXCEPT ![p] = "PushL4"]
    /\ UNCHANGED <<leftHat, rightHat, freelist, op, arg, result, localNode, localLeft, localRight, newNode, oldLeft, oldRight, valBag>>

PushL4(p) ==
    /\ pc[p] = "PushL4"
    /\ IF oldLeft[p] = NullAddr
       THEN \* Empty deque case - DCAS on both hats
            IF leftHat = NullAddr /\ rightHat = NullAddr
            THEN /\ leftHat' = newNode[p]
                 /\ rightHat' = newNode[p]
                 /\ valBag' = [valBag EXCEPT ![arg[p]] = @ + 1]
                 /\ pc' = [pc EXCEPT ![p] = "PushL5"]
            ELSE /\ pc' = [pc EXCEPT ![p] = "PushL2"]  \* Retry
                 /\ UNCHANGED <<leftHat, rightHat, valBag>>
       ELSE \* Non-empty deque - DCAS on leftHat and old left node's left pointer
            IF leftHat = oldLeft[p] /\ mem[oldLeft[p]].left = NullAddr
            THEN /\ leftHat' = newNode[p]
                 /\ mem' = [mem EXCEPT ![oldLeft[p]].left = newNode[p]]
                 /\ valBag' = [valBag EXCEPT ![arg[p]] = @ + 1]
                 /\ pc' = [pc EXCEPT ![p] = "PushL5"]
                 /\ UNCHANGED rightHat
            ELSE /\ pc' = [pc EXCEPT ![p] = "PushL2"]  \* Retry
                 /\ UNCHANGED <<leftHat, rightHat, mem, valBag>>
    /\ UNCHANGED <<freelist, op, arg, result, localNode, localLeft, localRight, newNode, oldLeft, oldRight>>

PushL5(p) ==
    /\ pc[p] = "PushL5"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ op' = [op EXCEPT ![p] = "none"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, arg, result, localNode, localLeft, localRight, newNode, oldLeft, oldRight, valBag>>

\* PushRight operation steps
PushR1(p) ==
    /\ pc[p] = "PushR1"
    /\ freelist /= {}
    /\ \E a \in freelist:
        /\ newNode' = [newNode EXCEPT ![p] = a]
        /\ freelist' = freelist \ {a}
        /\ mem' = [mem EXCEPT ![a] = [val |-> arg[p], left |-> NullAddr, right |-> NullAddr]]
    /\ pc' = [pc EXCEPT ![p] = "PushR2"]
    /\ UNCHANGED <<leftHat, rightHat, op, arg, result, localNode, localLeft, localRight, oldLeft, oldRight, valBag>>

PushR2(p) ==
    /\ pc[p] = "PushR2"
    /\ oldLeft' = [oldLeft EXCEPT ![p] = leftHat]
    /\ oldRight' = [oldRight EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PushR3"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, op, arg, result, localNode, localLeft, localRight, newNode, valBag>>

PushR3(p) ==
    /\ pc[p] = "PushR3"
    /\ mem' = [mem EXCEPT ![newNode[p]].left = oldRight[p]]
    /\ pc' = [pc EXCEPT ![p] = "PushR4"]
    /\ UNCHANGED <<leftHat, rightHat, freelist, op, arg, result, localNode, localLeft, localRight, newNode, oldLeft, oldRight, valBag>>

PushR4(p) ==
    /\ pc[p] = "PushR4"
    /\ IF oldRight[p] = NullAddr
       THEN \* Empty deque case
            IF leftHat = NullAddr /\ rightHat = NullAddr
            THEN /\ leftHat' = newNode[p]
                 /\ rightHat' = newNode[p]
                 /\ valBag' = [valBag EXCEPT ![arg[p]] = @ + 1]
                 /\ pc' = [pc EXCEPT ![p] = "PushR5"]
            ELSE /\ pc' = [pc EXCEPT ![p] = "PushR2"]
                 /\ UNCHANGED <<leftHat, rightHat, valBag>>
       ELSE \* Non-empty deque
            IF rightHat = oldRight[p] /\ mem[oldRight[p]].right = NullAddr
            THEN /\ rightHat' = newNode[p]
                 /\ mem' = [mem EXCEPT ![oldRight[p]].right = newNode[p]]
                 /\ valBag' = [valBag EXCEPT ![arg[p]] = @ + 1]
                 /\ pc' = [pc EXCEPT ![p] = "PushR5"]
                 /\ UNCHANGED leftHat
            ELSE /\ pc' = [pc EXCEPT ![p] = "PushR2"]
                 /\ UNCHANGED <<leftHat, rightHat, mem, valBag>>
    /\ UNCHANGED <<freelist, op, arg, result, localNode, localLeft, localRight, newNode, oldLeft, oldRight>>

PushR5(p) ==
    /\ pc[p] = "PushR5"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ op' = [op EXCEPT ![p] = "none"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, arg, result, localNode, localLeft, localRight, newNode, oldLeft, oldRight, valBag>>

\* PopLeft operation steps
PopL1(p) ==
    /\ pc[p] = "PopL1"
    /\ oldLeft' = [oldLeft EXCEPT ![p] = leftHat]
    /\ oldRight' = [oldRight EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PopL2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, op, arg, result, localNode, localLeft, localRight, newNode, valBag>>

PopL2(p) ==
    /\ pc[p] = "PopL2"
    /\ IF oldLeft[p] = NullAddr
       THEN \* Empty deque
            /\ result' = [result EXCEPT ![p] = NullAddr]
            /\ pc' = [pc EXCEPT ![p] = "PopL5"]
            /\ UNCHANGED <<localRight>>
       ELSE
            /\ localRight' = [localRight EXCEPT ![p] = mem[oldLeft[p]].right]
            /\ pc' = [pc EXCEPT ![p] = "PopL3"]
            /\ UNCHANGED result
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, op, arg, localNode, localLeft, newNode, oldLeft, oldRight, valBag>>

PopL3(p) ==
    /\ pc[p] = "PopL3"
    /\ IF oldLeft[p] = oldRight[p]
       THEN \* Single element case - DCAS on both hats
            IF leftHat = oldLeft[p] /\ rightHat = oldRight[p]
            THEN /\ leftHat' = NullAddr
                 /\ rightHat' = NullAddr
                 /\ result' = [result EXCEPT ![p] = mem[oldLeft[p]].val]
                 /\ freelist' = freelist \cup {oldLeft[p]}
                 /\ valBag' = [valBag EXCEPT ![mem[oldLeft[p]].val] = @ - 1]
                 /\ pc' = [pc EXCEPT ![p] = "PopL5"]
            ELSE /\ pc' = [pc EXCEPT ![p] = "PopL1"]
                 /\ UNCHANGED <<leftHat, rightHat, result, freelist, valBag>>
       ELSE \* Multiple elements
            IF leftHat = oldLeft[p] /\ localRight[p] /= NullAddr /\ mem[localRight[p]].left = oldLeft[p]
            THEN /\ leftHat' = localRight[p]
                 /\ mem' = [mem EXCEPT ![localRight[p]].left = NullAddr]
                 /\ result' = [result EXCEPT ![p] = mem[oldLeft[p]].val]
                 /\ freelist' = freelist \cup {oldLeft[p]}
                 /\ valBag' = [valBag EXCEPT ![mem[oldLeft[p]].val] = @ - 1]
                 /\ pc' = [pc EXCEPT ![p] = "PopL5"]
                 /\ UNCHANGED rightHat
            ELSE /\ pc' = [pc EXCEPT ![p] = "PopL1"]
                 /\ UNCHANGED <<leftHat, rightHat, mem, result, freelist, valBag>>
    /\ UNCHANGED <<op, arg, localNode, localLeft, localRight, newNode, oldLeft, oldRight>>

PopL5(p) ==
    /\ pc[p] = "PopL5"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ op' = [op EXCEPT ![p] = "none"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, arg, result, localNode, localLeft, localRight, newNode, oldLeft, oldRight, valBag>>

\* PopRight operation steps
PopR1(p) ==
    /\ pc[p] = "PopR1"
    /\ oldLeft' = [oldLeft EXCEPT ![p] = leftHat]
    /\ oldRight' = [oldRight EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PopR2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, op, arg, result, localNode, localLeft, localRight, newNode, valBag>>

PopR2(p) ==
    /\ pc[p] = "PopR2"
    /\ IF oldRight[p] = NullAddr
       THEN \* Empty deque
            /\ result' = [result EXCEPT ![p] = NullAddr]
            /\ pc' = [pc EXCEPT ![p] = "PopR5"]
            /\ UNCHANGED <<localLeft>>
       ELSE
            /\ localLeft' = [localLeft EXCEPT ![p] = mem[oldRight[p]].left]
            /\ pc' = [pc EXCEPT ![p] = "PopR3"]
            /\ UNCHANGED result
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, op, arg, localNode, localRight, newNode, oldLeft, oldRight, valBag>>

PopR3(p) ==
    /\ pc[p] = "PopR3"
    /\ IF oldLeft[p] = oldRight[p]
       THEN \* Single element case
            IF leftHat = oldLeft[p] /\ rightHat = oldRight[p]
            THEN /\ leftHat' = NullAddr
                 /\ rightHat' = NullAddr
                 /\ result' = [result EXCEPT ![p] = mem[oldRight[p]].val]
                 /\ freelist' = freelist \cup {oldRight[p]}
                 /\ valBag' = [valBag EXCEPT ![mem[oldRight[p]].val] = @ - 1]
                 /\ pc' = [pc EXCEPT ![p] = "PopR5"]
            ELSE /\ pc' = [pc EXCEPT ![p] = "PopR1"]
                 /\ UNCHANGED <<leftHat, rightHat, result, freelist, valBag>>
       ELSE \* Multiple elements
            IF rightHat = oldRight[p] /\ localLeft[p] /= NullAddr /\ mem[localLeft[p]].right = oldRight[p]
            THEN /\ rightHat' = localLeft[p]
                 /\ mem' = [mem EXCEPT ![localLeft[p]].right = NullAddr]
                 /\ result' = [result EXCEPT ![p] = mem[oldRight[p]].val]
                 /\ freelist' = freelist \cup {oldRight[p]}
                 /\ valBag' = [valBag EXCEPT ![mem[oldRight[p]].val] = @ - 1]
                 /\ pc' = [pc EXCEPT ![p] = "PopR5"]
                 /\ UNCHANGED leftHat
            ELSE /\ pc' = [pc EXCEPT ![p] = "PopR1"]
                 /\ UNCHANGED <<leftHat, rightHat, mem, result, freelist, valBag>>
    /\ UNCHANGED <<op, arg, localNode, localLeft, localRight, newNode, oldLeft, oldRight>>

PopR5(p) ==
    /\ pc[p] = "PopR5"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ op' = [op EXCEPT ![p] = "none"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, arg, result, localNode, localLeft, localRight, newNode, oldLeft, oldRight, valBag>>

\* Next state relation
Next ==
    \E p \in Procs:
        \/ TestChoose(p)
        \/ PushL1(p) \/ PushL2(p) \/ PushL3(p) \/ PushL4(p) \/ PushL5(p)
        \/ PushR1(p) \/ PushR2(p) \/ PushR3(p) \/ PushR4(p) \/ PushR5(p)
        \/ PopL1(p) \/ PopL2(p) \/ PopL3(p) \/ PopL5(p)
        \/ PopR1(p) \/ PopR2(p) \/ PopR3(p) \/ PopR5(p)

\* Fairness: weak fairness for all process actions
Fairness ==
    \A p \in Procs:
        /\ WF_vars(TestChoose(p))
        /\ WF_vars(PushL1(p)) /\ WF_vars(PushL2(p)) /\ WF_vars(PushL3(p)) 
        /\ WF_vars(PushL4(p)) /\ WF_vars(PushL5(p))
        /\ WF_vars(PushR1(p)) /\ WF_vars(PushR2(p)) /\ WF_vars(PushR3(p))
        /\ WF_vars(PushR4(p)) /\ WF_vars(PushR5(p))
        /\ WF_vars(PopL1(p)) /\ WF_vars(PopL2(p)) /\ WF_vars(PopL3(p)) /\ WF_vars(PopL5(p))
        /\ WF_vars(PopR1(p)) /\ WF_vars(PopR2(p)) /\ WF_vars(PopR3(p)) /\ WF_vars(PopR5(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariant: valBag counts are non-negative
ValBagNonNegative == \A v \in Values: valBag[v] >= 0

\* Safety invariant: deque structure consistency
DequeConsistency ==
    /\ (leftHat = NullAddr) <=> (rightHat = NullAddr)
    /\ \A v \in Values: valBag[v] >= 0

\* Liveness property: every test process returns to T1 infinitely often
LivenessT1 == \A p \in Procs: []<>(pc[p] = "T1")

================================================================================