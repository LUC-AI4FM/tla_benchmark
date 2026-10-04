---------------------------- MODULE LockFreeDeque ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Clients,        \* Set of client identifiers
    Values,         \* Set of possible values in the deque
    MaxNodes,       \* Maximum number of node slots in the pool
    NullNode,       \* Distinguished null node identifier
    EmptyResult,    \* Result code for pop on empty deque
    FullResult,     \* Result code for allocation failure
    OkResult        \* Result code for successful push

ASSUME NullNode \notin 1..MaxNodes
ASSUME EmptyResult \notin Values
ASSUME FullResult \notin Values
ASSUME OkResult \notin Values

NodeIds == 1..MaxNodes
AllNodeIds == NodeIds \cup {NullNode}

VARIABLES
    \* Deque structure
    head,           \* Head sentinel node id
    tail,           \* Tail sentinel node id
    nodes,          \* Function: NodeId -> [val: Value \cup {NULL}, left: NodeId, right: NodeId, allocated: BOOLEAN]
    freePool,       \* Set of free node ids
    
    \* Client state
    clientState,    \* Function: Client -> client operation state
    clientOp,       \* Function: Client -> current operation type
    clientArg,      \* Function: Client -> operation argument (value for push)
    clientResult,   \* Function: Client -> operation result
    
    \* Linearization tracking
    linearHistory,  \* Sequence of completed operations for linearizability
    pendingOps,     \* Set of operations in progress
    
    \* Ghost variables for memory safety
    reachableNodes  \* Set of nodes currently reachable from head/tail

vars == <<head, tail, nodes, freePool, clientState, clientOp, clientArg, 
          clientResult, linearHistory, pendingOps, reachableNodes>>

NULL == "NULL"

OpTypes == {"idle", "pushLeft", "pushRight", "popLeft", "popRight"}

ClientStates == {"idle", "allocating", "linking", "completing", "retrying"}

\* Initialize a fresh node record
FreshNode == [val |-> NULL, left |-> NullNode, right |-> NullNode, allocated |-> FALSE]

\* Initialize sentinel node (allocated, self-linked initially)
SentinelNode(id) == [val |-> NULL, left |-> id, right |-> id, allocated |-> TRUE]

TypeOK ==
    /\ head \in NodeIds
    /\ tail \in NodeIds
    /\ nodes \in [NodeIds -> [val: Values \cup {NULL}, 
                              left: AllNodeIds, 
                              right: AllNodeIds, 
                              allocated: BOOLEAN]]
    /\ freePool \subseteq NodeIds
    /\ clientState \in [Clients -> ClientStates]
    /\ clientOp \in [Clients -> OpTypes]
    /\ clientArg \in [Clients -> Values \cup {NULL}]
    /\ clientResult \in [Clients -> Values \cup {EmptyResult, FullResult, OkResult, NULL}]
    /\ linearHistory \in Seq([op: OpTypes, client: Clients, arg: Values \cup {NULL}, 
                              result: Values \cup {EmptyResult, FullResult, OkResult, NULL}])
    /\ pendingOps \subseteq Clients
    /\ reachableNodes \subseteq NodeIds

\* Compute reachable nodes from head and tail
ComputeReachable ==
    LET 
        RECURSIVE ReachRight(_, _, _)
        ReachRight(n, visited, limit) ==
            IF n = NullNode \/ n \in visited \/ limit = 0 THEN visited
            ELSE ReachRight(nodes[n].right, visited \cup {n}, limit - 1)
        
        RECURSIVE ReachLeft(_, _, _)
        ReachLeft(n, visited, limit) ==
            IF n = NullNode \/ n \in visited \/ limit = 0 THEN visited
            ELSE ReachLeft(nodes[n].left, visited \cup {n}, limit - 1)
    IN
        ReachRight(head, {}, MaxNodes + 2) \cup ReachLeft(tail, {}, MaxNodes + 2)

Init ==
    /\ head = 1  \* Head sentinel
    /\ tail = 2  \* Tail sentinel
    \* Initialize sentinels: head.right = tail, tail.left = head
    /\ nodes = [n \in NodeIds |->
                  IF n = 1 THEN [val |-> NULL, left |-> NullNode, right |-> 2, allocated |-> TRUE]
                  ELSE IF n = 2 THEN [val |-> NULL, left |-> 1, right |-> NullNode, allocated |-> TRUE]
                  ELSE FreshNode]
    /\ freePool = NodeIds \ {1, 2}
    /\ clientState = [c \in Clients |-> "idle"]
    /\ clientOp = [c \in Clients |-> "idle"]
    /\ clientArg = [c \in Clients |-> NULL]
    /\ clientResult = [c \in Clients |-> NULL]
    /\ linearHistory = <<>>
    /\ pendingOps = {}
    /\ reachableNodes = {1, 2}

\* Client begins a push operation
BeginPush(c, side, val) ==
    /\ clientState[c] = "idle"
    /\ val \in Values
    /\ clientState' = [clientState EXCEPT ![c] = "allocating"]
    /\ clientOp' = [clientOp EXCEPT ![c] = side]
    /\ clientArg' = [clientArg EXCEPT ![c] = val]
    /\ clientResult' = [clientResult EXCEPT ![c] = NULL]
    /\ pendingOps' = pendingOps \cup {c}
    /\ UNCHANGED <<head, tail, nodes, freePool, linearHistory, reachableNodes>>

\* Allocate a node for push - may fail if pool empty
AllocateNode(c) ==
    /\ clientState[c] = "allocating"
    /\ clientOp[c] \in {"pushLeft", "pushRight"}
    /\ IF freePool = {} THEN
         \* Allocation fails
         /\ clientState' = [clientState EXCEPT ![c] = "completing"]
         /\ clientResult' = [clientResult EXCEPT ![c] = FullResult]
         /\ UNCHANGED <<head, tail, nodes, freePool, reachableNodes>>
       ELSE
         \* Allocate a free node
         /\ \E n \in freePool:
              /\ freePool' = freePool \ {n}
              /\ nodes' = [nodes EXCEPT ![n] = [val |-> clientArg[c], 
                                                 left |-> NullNode, 
                                                 right |-> NullNode, 
                                                 allocated |-> TRUE]]
              /\ clientState' = [clientState EXCEPT ![c] = "linking"]
              /\ clientResult' = [clientResult EXCEPT ![c] = NULL]
              /\ reachableNodes' = reachableNodes \cup {n}
    /\ UNCHANGED <<head, tail, clientOp, clientArg, linearHistory, pendingOps>>

\* Find the allocated node for this client (ghost helper)
AllocatedNodeFor(c) ==
    CHOOSE n \in NodeIds : 
        /\ nodes[n].allocated 
        /\ nodes[n].val = clientArg[c]
        /\ n \notin {head, tail}
        /\ nodes[n].left = NullNode
        /\ nodes[n].right = NullNode

\* Atomic double-CAS for pushLeft: update head's neighbor and new node links
DoCASPushLeft(c) ==
    /\ clientState[c] = "linking"
    /\ clientOp[c] = "pushLeft"
    /\ LET newNode == CHOOSE n \in NodeIds : 
                        /\ nodes[n].allocated 
                        /\ nodes[n].val = clientArg[c]
                        /\ n \notin {head, tail}
           oldFirst == nodes[head].right
       IN
         \* Atomic DCAS: update head.right, oldFirst.left, newNode links
         /\ nodes' = [nodes EXCEPT 
              ![newNode].left = head,
              ![newNode].right = oldFirst,
              ![head].right = newNode,
              ![oldFirst].left = newNode]
         /\ clientState' = [clientState EXCEPT ![c] = "completing"]
         /\ clientResult' = [clientResult EXCEPT ![c] = OkResult]
    /\ UNCHANGED <<head, tail, freePool, clientOp, clientArg, linearHistory, pendingOps, reachableNodes>>

\* Atomic double-CAS for pushRight: update tail's neighbor and new node links
DoCASPushRight(c) ==
    /\ clientState[c] = "linking"
    /\ clientOp[c] = "pushRight"
    /\ LET newNode == CHOOSE n \in NodeIds : 
                        /\ nodes[n].allocated 
                        /\ nodes[n].val = clientArg[c]
                        /\ n \notin {head, tail}
           oldLast == nodes[tail].left
       IN
         \* Atomic DCAS: update tail.left, oldLast.right, newNode links
         /\ nodes' = [nodes EXCEPT 
              ![newNode].right = tail,
              ![newNode].left = oldLast,
              ![tail].left = newNode,
              ![oldLast].right = newNode]
         /\ clientState' = [clientState EXCEPT ![c] = "completing"]
         /\ clientResult' = [clientResult EXCEPT ![c] = OkResult]
    /\ UNCHANGED <<head, tail, freePool, clientOp, clientArg, linearHistory, pendingOps, reachableNodes>>

\* Client begins a pop operation
BeginPop(c, side) ==
    /\ clientState[c] = "idle"
    /\ clientState' = [clientState EXCEPT ![c] = "linking"]
    /\ clientOp' = [clientOp EXCEPT ![c] = side]
    /\ clientArg' = [clientArg EXCEPT ![c] = NULL]
    /\ clientResult' = [clientResult EXCEPT ![c] = NULL]
    /\ pendingOps' = pendingOps \cup {c}
    /\ UNCHANGED <<head, tail, nodes, freePool, linearHistory, reachableNodes>>

\* Atomic pop from left
DoCASPopLeft(c) ==
    /\ clientState[c] = "linking"
    /\ clientOp[c] = "popLeft"
    /\ LET firstNode == nodes[head].right
       IN
         IF firstNode = tail THEN
           \* Deque is empty
           /\ clientState' = [clientState EXCEPT ![c] = "completing"]
           /\ clientResult' = [clientResult EXCEPT ![c] = EmptyResult]
           /\ UNCHANGED <<head, tail, nodes, freePool, reachableNodes>>
         ELSE
           \* Remove first node: DCAS head.right and secondNode.left
           LET secondNode == nodes[firstNode].right
               poppedVal == nodes[firstNode].val
           IN
             /\ nodes' = [nodes EXCEPT 
                  ![head].right = secondNode,
                  ![secondNode].left = head,
                  ![firstNode].allocated = FALSE,
                  ![firstNode].left = NullNode,
                  ![firstNode].right = NullNode]
             /\ freePool' = freePool \cup {firstNode}
             /\ clientState' = [clientState EXCEPT ![c] = "completing"]
             /\ clientResult' = [clientResult EXCEPT ![c] = poppedVal]
             /\ reachableNodes' = reachableNodes \ {firstNode}
    /\ UNCHANGED <<head, tail, clientOp, clientArg, linearHistory, pendingOps>>

\* Atomic pop from right
DoCASPopRight(c) ==
    /\ clientState[c] = "linking"
    /\ clientOp[c] = "popRight"
    /\ LET lastNode == nodes[tail].left
       IN
         IF lastNode = head THEN
           \* Deque is empty
           /\ clientState' = [clientState EXCEPT ![c] = "completing"]
           /\ clientResult' = [clientResult EXCEPT ![c] = EmptyResult]
           /\ UNCHANGED <<head, tail, nodes, freePool, reachableNodes>>
         ELSE
           \* Remove last node: DCAS tail.left and secondLastNode.right
           LET secondLastNode == nodes[lastNode].left
               poppedVal == nodes[lastNode].val
           IN
             /\ nodes' = [nodes EXCEPT 
                  ![tail].left = secondLastNode,
                  ![secondLastNode].right = tail,
                  ![lastNode].allocated = FALSE,
                  ![lastNode].left = NullNode,
                  ![lastNode].right = NullNode]
             /\ freePool' = freePool \cup {lastNode}
             /\ clientState' = [clientState EXCEPT ![c] = "completing"]
             /\ clientResult' = [clientResult EXCEPT ![c] = poppedVal]
             /\ reachableNodes' = reachableNodes \ {lastNode}
    /\ UNCHANGED <<head, tail, clientOp, clientArg, linearHistory, pendingOps>>

\* Complete operation and record in history
CompleteOp(c) ==
    /\ clientState[c] = "completing"
    /\ linearHistory' = Append(linearHistory, 
         [op |-> clientOp[c], 
          client |-> c, 
          arg |-> clientArg[c], 
          result |-> clientResult[c]])
    /\ clientState' = [clientState EXCEPT ![c] = "idle"]
    /\ clientOp' = [clientOp EXCEPT ![c] = "idle"]
    /\ clientArg' = [clientArg EXCEPT ![c] = NULL]
    /\ pendingOps' = pendingOps \ {c}
    /\ UNCHANGED <<head, tail, nodes, freePool, clientResult, reachableNodes>>

\* Garbage collector: reclaim unreachable nodes
GarbageCollect ==
    /\ \E n \in NodeIds \ {head, tail}:
         /\ nodes[n].allocated
         /\ n \notin reachableNodes
         /\ nodes' = [nodes EXCEPT ![n] = FreshNode]
         /\ freePool' = freePool \cup {n}
    /\ UNCHANGED <<head, tail, clientState, clientOp, clientArg, clientResult, 
                   linearHistory, pendingOps, reachableNodes>>

\* Retry operation on conflict (simplified - restart from beginning)
RetryOp(c) ==
    /\ clientState[c] = "retrying"
    /\ clientState' = [clientState EXCEPT ![c] = 
         IF clientOp[c] \in {"pushLeft", "pushRight"} THEN "allocating" ELSE "linking"]
    /\ UNCHANGED <<head, tail, nodes, freePool, clientOp, clientArg, clientResult,
                   linearHistory, pendingOps, reachableNodes>>

Next ==
    \/ \E c \in Clients, v \in Values: BeginPush(c, "pushLeft", v)
    \/ \E c \in Clients, v \in Values: BeginPush(c, "pushRight", v)
    \/ \E c \in Clients: BeginPop(c, "popLeft")
    \/ \E c \in Clients: BeginPop(c, "popRight")
    \/ \E c \in Clients: AllocateNode(c)
    \/ \E c \in Clients: DoCASPushLeft(c)
    \/ \E c \in Clients: DoCASPushRight(c)
    \/ \E c \in Clients: DoCASPopLeft(c)
    \/ \E c \in Clients: DoCASPopRight(c)
    \/ \E c \in Clients: CompleteOp(c)
    \/ \E c \in Clients: RetryOp(c)
    \/ GarbageCollect

\* Fairness: each client action is weakly fair
Fairness ==
    /\ \A c \in Clients: WF_vars(AllocateNode(c))
    /\ \A c \in Clients: WF_vars(DoCASPushLeft(c))
    /\ \A c \in Clients: WF_vars(DoCASPushRight(c))
    /\ \A c \in Clients: WF_vars(DoCASPopLeft(c))
    /\ \A c \in Clients: WF_vars(DoCASPopRight(c))
    /\ \A c \in Clients: WF_vars(CompleteOp(c))
    /\ \A c \in Clients: WF_vars(RetryOp(c))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ====================