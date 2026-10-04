---------------------------- MODULE LockFreeDeque ----------------------------
(***************************************************************************)
(* Lock-Free Double-Ended Queue (Deque) using Double Compare-And-Swap      *)
(* This specification models a concurrent deque that supports push and pop *)
(* operations from both ends using DCAS as the synchronization primitive.  *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Procs,          \* Set of process identifiers
    Values,         \* Set of values that can be stored in the deque
    Addresses,      \* Set of memory addresses for nodes
    MaxOps          \* Maximum operations per process (for bounded model checking)

VARIABLES
    \* Memory model
    mem,            \* mem[addr] = [left |-> addr, right |-> addr, val |-> value]
    freeList,       \* Set of available addresses
    
    \* Deque structure
    leftSentinel,   \* Address of left sentinel node
    rightSentinel,  \* Address of right sentinel node
    
    \* Process local state
    pc,             \* pc[p] = program counter for process p
    op,             \* op[p] = current operation type for process p
    localAddr,      \* localAddr[p] = locally allocated address
    localVal,       \* localVal[p] = value being pushed/popped
    result,         \* result[p] = result of last operation
    readLeft,       \* readLeft[p] = snapshot of left pointer
    readRight,      \* readRight[p] = snapshot of right pointer
    readNode,       \* readNode[p] = snapshot of node being operated on
    opCount,        \* opCount[p] = number of operations completed
    
    \* Ghost variables for verification
    pushed,         \* Set of (value, unique_id) pairs that have been pushed
    popped,         \* Set of (value, unique_id) pairs that have been popped
    inDeque,        \* Set of (value, unique_id) pairs currently in deque
    nextId          \* Counter for generating unique push identifiers

vars == <<mem, freeList, leftSentinel, rightSentinel, pc, op, localAddr, 
          localVal, result, readLeft, readRight, readNode, opCount,
          pushed, popped, inDeque, nextId>>

NULL == CHOOSE n : n \notin Addresses

Status == {"okay", "empty", "full", "none"}
Operations == {"pushLeft", "pushRight", "popLeft", "popRight", "idle"}
ProgramCounters == {"idle", "chooseOp", 
                    "pushL_alloc", "pushL_read", "pushL_dcas", "pushL_done",
                    "pushR_alloc", "pushR_read", "pushR_dcas", "pushR_done",
                    "popL_read", "popL_check", "popL_dcas", "popL_done",
                    "popR_read", "popR_check", "popR_dcas", "popR_done"}

(***************************************************************************)
(* Type Invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ mem \in [Addresses -> [left : Addresses \cup {NULL}, 
                               right : Addresses \cup {NULL}, 
                               val : Values \cup {NULL}]]
    /\ freeList \subseteq Addresses
    /\ leftSentinel \in Addresses
    /\ rightSentinel \in Addresses
    /\ pc \in [Procs -> ProgramCounters]
    /\ op \in [Procs -> Operations]
    /\ localAddr \in [Procs -> Addresses \cup {NULL}]
    /\ localVal \in [Procs -> Values \cup {NULL}]
    /\ result \in [Procs -> Status]
    /\ opCount \in [Procs -> Nat]

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init ==
    \* Initialize sentinels - pick two distinct addresses
    /\ leftSentinel \in Addresses
    /\ rightSentinel \in Addresses \ {leftSentinel}
    \* Initialize memory with sentinels pointing to each other (empty deque)
    /\ mem = [a \in Addresses |-> 
                IF a = leftSentinel 
                THEN [left |-> NULL, right |-> rightSentinel, val |-> NULL]
                ELSE IF a = rightSentinel
                THEN [left |-> leftSentinel, right |-> NULL, val |-> NULL]
                ELSE [left |-> NULL, right |-> NULL, val |-> NULL]]
    /\ freeList = Addresses \ {leftSentinel, rightSentinel}
    \* Process state
    /\ pc = [p \in Procs |-> "idle"]
    /\ op = [p \in Procs |-> "idle"]
    /\ localAddr = [p \in Procs |-> NULL]
    /\ localVal = [p \in Procs |-> NULL]
    /\ result = [p \in Procs |-> "none"]
    /\ readLeft = [p \in Procs |-> NULL]
    /\ readRight = [p \in Procs |-> NULL]
    /\ readNode = [p \in Procs |-> [left |-> NULL, right |-> NULL, val |-> NULL]]
    /\ opCount = [p \in Procs |-> 0]
    \* Ghost state
    /\ pushed = {}
    /\ popped = {}
    /\ inDeque = {}
    /\ nextId = 0

(***************************************************************************)
(* Helper: Allocate a node from free list                                  *)
(***************************************************************************)
Allocate(p) ==
    IF freeList = {} 
    THEN /\ localAddr' = [localAddr EXCEPT ![p] = NULL]
         /\ UNCHANGED freeList
    ELSE \E a \in freeList:
         /\ localAddr' = [localAddr EXCEPT ![p] = a]
         /\ freeList' = freeList \ {a}

(***************************************************************************)
(* Helper: Free a node back to free list                                   *)
(***************************************************************************)
Free(addr) ==
    freeList' = freeList \cup {addr}

(***************************************************************************)
(* Process chooses next operation                                          *)
(***************************************************************************)
ChooseOperation(p) ==
    /\ pc[p] = "idle"
    /\ opCount[p] < MaxOps
    /\ \E operation \in {"pushLeft", "pushRight", "popLeft", "popRight"}:
        /\ op' = [op EXCEPT ![p] = operation]
        /\ pc' = [pc EXCEPT ![p] = "chooseOp"]
        /\ result' = [result EXCEPT ![p] = "none"]
    /\ UNCHANGED <<mem, freeList, leftSentinel, rightSentinel, 
                   localAddr, localVal, readLeft, readRight, readNode, opCount,
                   pushed, popped, inDeque, nextId>>

StartOperation(p) ==
    /\ pc[p] = "chooseOp"
    /\ \E v \in Values:
        /\ localVal' = [localVal EXCEPT ![p] = v]
        /\ CASE op[p] = "pushLeft" -> pc' = [pc EXCEPT ![p] = "pushL_alloc"]
             [] op[p] = "pushRight" -> pc' = [pc EXCEPT ![p] = "pushR_alloc"]
             [] op[p] = "popLeft" -> pc' = [pc EXCEPT ![p] = "popL_read"]
             [] op[p] = "popRight" -> pc' = [pc EXCEPT ![p] = "popR_read"]
    /\ UNCHANGED <<mem, freeList, leftSentinel, rightSentinel,
                   localAddr, result, readLeft, readRight, readNode, opCount, op,
                   pushed, popped, inDeque, nextId>>

(***************************************************************************)
(* Push Left Operation                                                     *)
(***************************************************************************)
PushL_Alloc(p) ==
    /\ pc[p] = "pushL_alloc"
    /\ Allocate(p)
    /\ IF freeList = {}
       THEN /\ pc' = [pc EXCEPT ![p] = "pushL_done"]
            /\ result' = [result EXCEPT ![p] = "full"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "pushL_read"]
            /\ UNCHANGED result
    /\ UNCHANGED <<mem, leftSentinel, rightSentinel, localVal, 
                   readLeft, readRight, readNode, opCount, op,
                   pushed, popped, inDeque, nextId>>

PushL_Read(p) ==
    /\ pc[p] = "pushL_read"
    /\ localAddr[p] # NULL
    /\ readLeft' = [readLeft EXCEPT ![p] = leftSentinel]
    /\ readRight' = [readRight EXCEPT ![p] = mem[leftSentinel].right]
    /\ pc' = [pc EXCEPT ![p] = "pushL_dcas"]
    /\ UNCHANGED <<mem, freeList, leftSentinel, rightSentinel, localAddr, localVal,
                   result, readNode, opCount, op, pushed, popped, inDeque, nextId>>

PushL_DCAS(p) ==
    /\ pc[p] = "pushL_dcas"
    /\ localAddr[p] # NULL
    /\ LET ls == readLeft[p]
           rs == readRight[p]
           newNode == localAddr[p]
       IN
       \* DCAS: Check leftSentinel.right == rs AND rs.left == ls
       IF mem[ls].right = rs /\ mem[rs].left = ls
       THEN \* Success: atomically update both pointers and insert node
            /\ mem' = [mem EXCEPT 
                        ![newNode] = [left |-> ls, right |-> rs, val |-> localVal[p]],
                        ![ls].right = newNode,
                        ![rs].left = newNode]
            /\ result' = [result EXCEPT ![p] = "okay"]
            /\ pc' = [pc EXCEPT ![p] = "pushL_done"]
            \* Ghost update
            /\ pushed' = pushed \cup {<<localVal[p], nextId>>}
            /\ inDeque' = inDeque \cup {<<localVal[p], nextId>>}
            /\ nextId' = nextId + 1
       ELSE \* Failure: retry
            /\ pc' = [pc EXCEPT ![p] = "pushL_read"]
            /\ UNCHANGED <<mem, result, pushed, inDeque, nextId>>
    /\ UNCHANGED <<freeList, leftSentinel, rightSentinel, localAddr, localVal,
                   readLeft, readRight, readNode, opCount, op, popped>>

PushL_Done(p) ==
    /\ pc[p] = "pushL_done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ op' = [op EXCEPT ![p] = "idle"]
    /\ opCount' = [opCount EXCEPT ![p] = opCount[p] + 1]
    /\ localAddr' = [localAddr EXCEPT ![p] = NULL]
    /\ localVal' = [localVal EXCEPT ![p] = NULL]
    /\ UNCHANGED <<mem, freeList, leftSentinel, rightSentinel, 
                   result, readLeft, readRight, readNode,
                   pushed, popped, inDeque, nextId>>

(***************************************************************************)
(* Push Right Operation                                                    *)
(***************************************************************************)
PushR_Alloc(p) ==
    /\ pc[p] = "pushR_alloc"
    /\ Allocate(p)
    /\ IF freeList = {}
       THEN /\ pc' = [pc EXCEPT ![p] = "pushR_done"]
            /\ result' = [result EXCEPT ![p] = "full"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "pushR_read"]
            /\ UNCHANGED result
    /\ UNCHANGED <<mem, leftSentinel, rightSentinel, localVal,
                   readLeft, readRight, readNode, opCount, op,
                   pushed, popped, inDeque, nextId>>

PushR_Read(p) ==
    /\ pc[p] = "pushR_read"
    /\ localAddr[p] # NULL
    /\ readRight' = [readRight EXCEPT ![p] = rightSentinel]
    /\ readLeft' = [readLeft EXCEPT ![p] = mem[rightSentinel].left]
    /\ pc' = [pc EXCEPT ![p] = "pushR_dcas"]
    /\ UNCHANGED <<mem, freeList, leftSentinel, rightSentinel, localAddr, localVal,
                   result, readNode, opCount, op, pushed, popped, inDeque, nextId>>

PushR_DCAS(p) ==
    /\ pc[p] = "pushR_dcas"
    /\ localAddr[p] # NULL
    /\ LET rs == readRight[p]
           ls == readLeft[p]
           newNode == localAddr[p]
       IN
       \* DCAS: Check rightSentinel.left == ls AND ls.right == rs
       IF mem[rs].left = ls /\ mem[ls].right = rs
       THEN \* Success
            /\ mem' = [mem EXCEPT
                        ![newNode] = [left |-> ls, right |-> rs, val |-> localVal[p]],
                        ![rs].left = newNode,
                        ![ls].right = newNode]
            /\ result' = [result EXCEPT ![p] = "okay"]
            /\ pc' = [pc EXCEPT ![p] = "pushR_done"]
            \* Ghost update
            /\ pushed' = pushed \cup {<<localVal[p], nextId>>}
            /\ inDeque' = inDeque \cup {<<localVal[p], nextId>>}
            /\ nextId' = nextId + 1
       ELSE \* Failure: retry
            /\ pc' = [pc EXCEPT ![p] = "pushR_read"]
            /\ UNCHANGED <<mem, result, pushed, inDeque, nextId>>
    /\ UNCHANGED <<freeList, leftSentinel, rightSentinel, localAddr, localVal,
                   readLeft, readRight, readNode, opCount, op, popped>>

PushR_Done(p) ==
    /\ pc[p] = "pushR_done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ op' = [op EXCEPT ![p] = "idle"]
    /\ opCount' = [opCount EXCEPT ![p] = opCount[p] + 1]
    /\ localAddr' = [localAddr EXCEPT ![p] = NULL]
    /\ localVal' = [localVal EXCEPT ![p] = NULL]
    /\ UNCHANGED <<mem, freeList, leftSentinel, rightSentinel,
                   result, readLeft, readRight, readNode,
                   pushed, popped, inDeque, nextId>>

(***************************************************************************)
(* Pop Left Operation                                                      *)
(***************************************************************************)
PopL_Read(p) ==
    /\ pc[p] = "popL_read"
    /\ readLeft' = [readLeft EXCEPT ![p] = leftSentinel]
    /\ LET firstNode == mem[leftSentinel].right
       IN /\ readNode' = [readNode EXCEPT ![p] = mem[firstNode]]
          /\ localAddr' = [localAddr EXCEPT ![p] = firstNode]
    /\ pc' = [pc EXCEPT ![p] = "popL_check"]
    /\ UNCHANGED <<mem, freeList, leftSentinel, rightSentinel, localVal,
                   result, readRight, opCount, op, pushed, popped, inDeque, nextId>>

PopL_Check(p) ==
    /\ pc[p] = "popL_check"
    /\ IF localAddr[p] = rightSentinel
       THEN \* Deque is empty
            /\ result' = [result EXCEPT ![p] = "empty"]
            /\ pc' = [pc EXCEPT ![p] = "popL_done"]
            /\ UNCHANGED <<mem, freeList, localVal, pushed, popped, inDeque, nextId>>
       ELSE \* Try to remove the node
            /\ localVal' = [localVal EXCEPT ![p] = readNode[p].val]
            /\ pc' = [pc EXCEPT ![p] = "popL_dcas"]
            /\ UNCHANGED <<mem, freeList, result, pushed, popped, inDeque, nextId>>
    /\ UNCHANGED <<leftSentinel, rightSentinel, localAddr,
                   readLeft, readRight, readNode, opCount, op>>

PopL_DCAS(p) ==
    /\ pc[p] = "popL_dcas"
    /\ LET ls == readLeft[p]
           node == localAddr[p]
           nodeRight == readNode[p].right
       IN
       \* DCAS: Check leftSentinel.right == node AND node.right.left == node
       IF mem[ls].right = node /\ mem[nodeRight].left = node
       THEN \* Success: remove node
            /\ mem' = [mem EXCEPT
                        ![ls].right = nodeRight,
                        ![nodeRight].left = ls,
                        ![node] = [left |-> NULL, right |-> NULL, val |-> NULL]]
            /\ Free(node)
            /\ result' = [result EXCEPT ![p] = "okay"]
            /\ pc' = [pc EXCEPT ![p] = "popL_done"]
            \* Ghost update - find matching entry in inDeque
            /\ \E id \in {i \in Nat : <<localVal[p], i>> \in inDeque}:
                /\ popped' = popped \cup {<<localVal[p], id>>}
                /\ inDeque' = inDeque \ {<<localVal[p], id>>}
            /\ UNCHANGED <<pushed, nextId>>
       ELSE \* Failure: retry
            /\ pc' = [pc EXCEPT ![p] = "popL_read"]
            /\ UNCHANGED <<mem, freeList, result, pushed, popped, inDeque, nextId>>
    /\ UNCHANGED <<leftSentinel, rightSentinel, localAddr, localVal,
                   readLeft, readRight, readNode, opCount, op>>

PopL_Done(p) ==
    /\ pc[p] = "popL_done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ op' = [op EXCEPT ![p] = "idle"]
    /\ opCount' = [opCount EXCEPT ![p] = opCount[p] + 1]
    /\ localAddr' = [localAddr EXCEPT ![p] = NULL]
    /\ localVal' = [localVal EXCEPT ![p] = NULL]
    /\ UNCHANGED <<mem, freeList, leftSentinel, rightSentinel,
                   result, readLeft, readRight, readNode,
                   pushed, popped, inDeque, nextId>>

(***************************************************************************)
(* Pop Right Operation                                                     *)
(***************************************************************************)
PopR_Read(p) ==
    /\ pc[p] = "popR_read"
    /\ readRight' = [readRight EXCEPT ![p] = rightSentinel]
    /\ LET lastNode == mem[rightSentinel].left
       IN /\ readNode' = [readNode EXCEPT ![p] = mem[lastNode]]
          /\ localAddr' = [localAddr EXCEPT ![p] = lastNode]
    /\ pc' = [pc EXCEPT ![p] = "popR_check"]
    /\ UNCHANGED <<mem, freeList, leftSentinel, rightSentinel, localVal,
                   result, readLeft, opCount, op, pushed, popped, inDeque, nextId>>

PopR_Check(p) ==
    /\ pc[p] = "popR_check"
    /\ IF localAddr[p] = leftSentinel
       THEN \* Deque is empty
            /\ result' = [result EXCEPT ![p] = "empty"]
            /\ pc' = [pc EXCEPT ![p] = "popR_done"]
            /\ UNCHANGED <<mem, freeList, localVal, pushed, popped, inDeque, nextId>>
       ELSE \* Try to remove the node
            /\ localVal' = [localVal EXCEPT ![p] = readNode[p].val]
            /\ pc' = [pc EXCEPT ![p] = "popR_dcas"]
            /\ UNCHANGED <<mem, freeList, result, pushed, popped, inDeque, nextId>>
    /\ UNCHANGED <<leftSentinel, rightSentinel, localAddr,
                   readLeft, readRight, readNode, opCount, op>>

PopR_DCAS(p) ==
    /\ pc[p] = "popR_dcas"
    /\ LET rs == readRight[p]
           node == localAddr[p]
           nodeLeft == readNode[p].left
       IN
       \* DCAS: Check rightSentinel.left == node AND node.left.right == node
       IF mem[rs].left = node /\ mem[nodeLeft].right = node
       THEN \* Success: remove node
            /\ mem' = [mem EXCEPT
                        ![rs].left = nodeLeft,
                        ![nodeLeft].right = rs,
                        ![node] = [left |-> NULL, right |-> NULL, val |-> NULL]]
            /\ Free(node)
            /\ result' = [result EXCEPT ![p] = "okay"]
            /\ pc' = [pc EXCEPT ![p] = "popR_done"]
            \* Ghost update
            /\ \E id \in {i \in Nat : <<localVal[p], i>> \in inDeque}:
                /\ popped' = popped \cup {<<localVal[p], id>>}
                /\ inDeque' = inDeque \ {<<localVal[p], id>>}
            /\ UNCHANGED <<pushed, nextId>>
       ELSE \* Failure: retry
            /\ pc' = [pc EXCEPT ![p] = "popR_read"]
            /\ UNCHANGED <<mem, freeList, result, pushed, popped, inDeque, nextId>>
    /\ UNCHANGED <<leftSentinel, rightSentinel, localAddr, localVal,
                   readLeft, readRight, readNode, opCount, op>>

PopR_Done(p) ==
    /\ pc[p] = "popR_done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ op' = [op EXCEPT ![p] = "idle"]
    /\ opCount' = [opCount EXCEPT ![p] = opCount[p] + 1]
    /\ localAddr' = [localAddr EXCEPT ![p] = NULL]
    /\ localVal' = [localVal EXCEPT ![p] = NULL]
    /\ UNCHANGED <<mem, freeList, leftSentinel, rightSentinel,
                   result, readLeft, readRight, readNode,
                   pushed, popped, inDeque, nextId>>

(***************************************************************************)
(* Next State Relation                                                     *)
(***************************************************************************)
ProcessStep(p) ==
    \/ ChooseOperation(p)
    \/ StartOperation(p)
    \/ PushL_Alloc(p)
    \/ PushL_Read(p)
    \/ PushL_DCAS(p)
    \/ PushL_Done(p)
    \/ PushR_Alloc(p)
    \/ PushR_Read(p)
    \/ PushR_DCAS(p)
    \/ PushR_Done(p)
    \/ PopL_Read(p)
    \/ PopL_Check(p)
    \/ PopL_DCAS(p)
    \/ PopL_Done(p)
    \/ PopR_Read(p)
    \/ PopR_Check(p)
    \/ PopR_DCAS(p)
    \/ PopR_Done(p)

Next == \E p \in Procs : ProcessStep(p)

(***************************************************************************)
(* Fairness Conditions                                                     *)
(***************************************************************************)
Fairness == \A p \in Procs : WF_vars(ProcessStep(p))

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

\* Every value popped was previously pushed
PoppedWasPushed ==
    \A item \in popped : item \in pushed

\* No duplicate pops - popped items don't overlap with items still in deque
NoDuplicatePops ==
    popped \cap inDeque = {}

\* No lost values - everything pushed is either in deque or was popped
NoLostValues ==
    \A item \in pushed : item \in inDeque \/ item \in popped

\* Structural integrity: sentinels always exist and are connected
StructuralIntegrity ==
    /\ leftSentinel \in Addresses
    /\ rightSentinel \in Addresses
    /\ leftSentinel # rightSentinel
    /\ mem[leftSentinel].left = NULL
    /\ mem[rightSentinel].right = NULL

\* The deque forms a proper doubly-linked list between sentinels
DequeConsistency ==
    LET 
        \* All nodes reachable from left sentinel going right
        ReachableRight == 
            {a \in Addresses : 
                \E n \in 0..Cardinality(Addresses) :
                    LET Walk[i \in 0..n] == 
                        IF i = 0 THEN leftSentinel
                        ELSE mem[Walk[i-1]].right
                    IN Walk[n] = a}
    IN
        rightSentinel \in ReachableRight

\* Combined safety invariant
SafetyInvariant ==
    /\ PoppedWasPushed
    /\ NoDuplicatePops
    /\ NoLostValues
    /\ StructuralIntegrity

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* Every process eventually completes its operations (under fairness)
EventualProgress ==
    \A p \in Procs : <>(opCount[p] = MaxOps)

\* If a process starts an operation, it eventually completes
OperationCompletion ==
    \A p \in Procs : (pc[p] # "idle") ~> (pc[p] = "idle")

=============================================================================