---------------------------- MODULE ConcurrentDeque ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Procs,          \* Set of process identifiers
    MaxAddr,        \* Maximum number of memory addresses
    Values,         \* Set of values that can be stored
    NullAddr        \* Null address constant

VARIABLES
    mem,            \* Memory: mapping from addresses to node records
    leftHat,        \* Left hat pointer (head of deque from left)
    rightHat,       \* Right hat pointer (head of deque from right)
    freelist,       \* Set of free addresses for allocation
    pc,             \* Program counter for each process
    op,             \* Current operation for each process
    localNode,      \* Local node address for each process
    localVal,       \* Local value for each process
    localLeft,      \* Local left pointer for each process
    localRight,     \* Local right pointer for each process
    oldLeftHat,     \* Saved left hat for CAS operations
    oldRightHat,    \* Saved right hat for CAS operations
    result,         \* Result of pop operations
    valBag          \* Multiset tracking values in the deque

vars == <<mem, leftHat, rightHat, freelist, pc, op, localNode, localVal, 
          localLeft, localRight, oldLeftHat, oldRightHat, result, valBag>>

Addresses == 1..MaxAddr

NullNode == [val |-> 0, left |-> NullAddr, right |-> NullAddr]

\* Initial state
Init ==
    /\ mem = [a \in Addresses |-> NullNode]
    /\ leftHat = NullAddr
    /\ rightHat = NullAddr
    /\ freelist = Addresses
    /\ pc = [p \in Procs |-> "T1"]
    /\ op = [p \in Procs |-> "none"]
    /\ localNode = [p \in Procs |-> NullAddr]
    /\ localVal = [p \in Procs |-> 0]
    /\ localLeft = [p \in Procs |-> NullAddr]
    /\ localRight = [p \in Procs |-> NullAddr]
    /\ oldLeftHat = [p \in Procs |-> NullAddr]
    /\ oldRightHat = [p \in Procs |-> NullAddr]
    /\ result = [p \in Procs |-> 0]
    /\ valBag = [v \in Values |-> 0]

\* Allocate a node from freelist
Allocate(p) ==
    /\ freelist /= {}
    /\ \E a \in freelist:
        /\ localNode' = [localNode EXCEPT ![p] = a]
        /\ freelist' = freelist \ {a}
    /\ UNCHANGED <<mem, leftHat, rightHat, pc, op, localVal, localLeft, 
                   localRight, oldLeftHat, oldRightHat, result, valBag>>

\* Free a node back to freelist
Free(p, addr) ==
    /\ addr /= NullAddr
    /\ freelist' = freelist \cup {addr}
    /\ mem' = [mem EXCEPT ![addr] = NullNode]

\* Test process chooses an operation
ChooseOp(p) ==
    /\ pc[p] = "T1"
    /\ \/ /\ freelist /= {}
          /\ \E v \in Values:
              /\ localVal' = [localVal EXCEPT ![p] = v]
              /\ \/ /\ op' = [op EXCEPT ![p] = "pushLeft"]
                    /\ pc' = [pc EXCEPT ![p] = "PL1"]
                 \/ /\ op' = [op EXCEPT ![p] = "pushRight"]
                    /\ pc' = [pc EXCEPT ![p] = "PR1"]
          /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localLeft,
                        localRight, oldLeftHat, oldRightHat, result, valBag>>
       \/ /\ \/ /\ op' = [op EXCEPT ![p] = "popLeft"]
                /\ pc' = [pc EXCEPT ![p] = "POL1"]
             \/ /\ op' = [op EXCEPT ![p] = "popRight"]
                /\ pc' = [pc EXCEPT ![p] = "POR1"]
          /\ UNCHANGED <<mem, leftHat, rightHat, freelist, localNode, localVal,
                        localLeft, localRight, oldLeftHat, oldRightHat, result, valBag>>

\* ============