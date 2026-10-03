-------------------------------- MODULE Deque --------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Procs,      \* The set of processes
    Values,     \* The set of values to store in the deque
    MemSize,    \* The total number of allocatable nodes in memory
    Nil         \* A special value for null pointers, distinct from addresses

ASSUME MemSize > 0
ASSUME Nil \notin 1..MemSize
ASSUME Cardinality(Procs) < MemSize

Addr == 1..MemSize
NodeRecord == [val: Values, left: Addr \cup {Nil}, right: Addr \cup {Nil}]
OpResult == {"OK", "Empty"}

VARIABLES 
    memory,     \* A map from addresses to node records
    left,       \* "Hat" pointer to the leftmost node
    right,      \* "Hat" pointer to the rightmost node
    freelist,   \* A sequence of available addresses
    pc,         \* Program counter for each process
    valBag,     \* A multiset of values in the deque, for the invariant
    \* Per-process local variables
    p_op,       \* The operation a process is performing
    p_val,      \* The value to be pushed
    p_l, p_r,   \* Local copies of left and right pointers
    p_new,      \* Address of a newly allocated node for a push
    p_node,     \* Address of the node being popped
    p_next,     \* Address of the node to the right of the one being popped
    p_res       \* The result of a pop operation

vars == << memory, left, right, freelist, pc, valBag, 
           p_op, p_val, p_l, p_r, p_new, p_node, p_next, p_res >>

\* A helper function to create a bag (multiset) from a sequence of nodes.
RECURSIVE _BuildBag(_)
_BuildBag(nodes) ==
    IF nodes = <<>>
    THEN [v \in Values |-> 0]
    ELSE LET restBag = _BuildBag(Tail(nodes))
             nodeVal = memory[Head(nodes)].val
         IN [v \in Values |-> IF v = nodeVal THEN restBag[v] + 1 ELSE restBag[v]]

\* A helper function to traverse the deque from left to right.
RECURSIVE _GetNodes(_)
_GetNodes(curr, visited) ==
    IF curr = Nil \/ curr \in visited
    THEN <<>>
    ELSE <<curr>> \o _GetNodes(memory[curr].right, visited \cup {curr})

CurrentDequeContents == _BuildBag(_GetNodes(left, {}))

-------------------------------- Invariants --------------------------------

TypeOK ==
    /\ memory \in [Addr -> NodeRecord]
    /\ left \in Addr \cup {Nil}
    /\ right \in Addr \cup {Nil}
    /\ IsASet(DOMAIN freelist) /\ DOMAIN freelist \subseteq 1..Len(freelist) /\ RANfreelist \subseteq Addr
    /\ pc \in [Procs -> STRING]
    /\ valBag \in [Values -> Nat]
    /\ p_op \in [Procs -> {"pushL", "pushR", "popL", "popR", "idle"}]
    /\ p_val \in [Procs -> Values]
    /\ p_l \in [Procs -> Addr \cup {Nil}]
    /\ p_r \in [Procs -> Addr \cup {Nil}]
    /\ p_new \in [Procs -> Addr \cup {Nil}]
    /\ p_node \in [Procs -> Addr \cup {Nil}]
    /\ p_next \in [Procs -> Addr \cup {Nil}]
    /\ p_res \in [Procs -> OpResult \cup Values]

\* The multiset of values in the abstract valBag matches the concrete deque.
Consistency == valBag = CurrentDequeContents

----------------------------- The Algorithm ------------------------------

Init ==
    /\ memory = [a \in Addr |-> [val |-> CHOOSE v \in Values, left |-> Nil, right |-> Nil]]
    /\ left = Nil
    /\ right = Nil
    /\ freelist = 1..MemSize
    /\ pc = [p \in Procs |-> "T1"]
    /\ valBag = [v \in Values |-> 0]
    /\ p_op = [p \in Procs |-> "idle"]
    /\ p_val = [p \in Procs |-> CHOOSE v \in Values]
    /\ p_l = [p \in Procs |-> Nil]
    /\ p_r = [p \in Procs |-> Nil]
    /\ p_new = [p \in Procs |-> Nil]
    /\ p_node = [p \in Procs |-> Nil]
    /\ p_next = [p \in Procs |-> Nil]
    /\ p_res = [p \in Procs |-> "OK"]

\* The test process starts a non-deterministic operation.
Test(self) ==
    /\ pc[self] = "T1"
    /\ \/ /\ \E v \in Values :
             /\ p_op' = [p_op EXCEPT ![self] = "pushL"]
             /\ p_val' = [p_val EXCEPT ![self] = v]
             /\ pc' = [pc EXCEPT ![self] = "Alloc"]
       \/ /\ \E v \in Values :
             /\ p_op' = [p_op EXCEPT ![self] = "pushR"]
             /\ p_val' = [p_val EXCEPT ![self] = v]
             /\ pc' = [pc EXCEPT ![self] = "Alloc"]
       \/ /\ p_op' = [p_op EXCEPT ![self] = "popL"]
          /\ pc' = [pc EXCEPT ![self] = "PopRead"]
       \/ /\ p_op' = [p_op EXCEPT ![self] = "popR"]
          /\ pc' = [pc EXCEPT ![self] = "PopRead"]
    /\ UNCHANGED << memory, left, right, freelist, valBag, 
                    p_l, p_r, p_new, p_node, p_next, p_res >>

\* Shared allocation step for push operations.
Alloc(self) ==
    /\ pc[self] = "Alloc"
    /\ freelist /= <<>>
    /\ p_new' = [p_new EXCEPT ![self] = Head(freelist)]
    /\ freelist' = Tail(freelist)
    /\ pc' = [pc EXCEPT ![self] = "PushRead"]
    /\ UNCHANGED << memory, left, right, valBag, p_op, p_val,
                    p_l, p_r, p_node, p_next, p_res >>

\* Push operations read the global state.
PushRead(self) ==
    /\ pc[self] = "PushRead"
    /\ p_l' = [p_l EXCEPT ![self] = left]
    /\ p_r' = [p_r EXCEPT ![self] = right]
    /\ pc' = [pc EXCEPT ![self] = "PushCommit"]
    /\ UNCHANGED << memory, left, right, freelist, valBag, p_op, p_val,
                    p_new, p_node, p_next, p_res >>
    
\* Push operations attempt to commit their changes.
PushCommit(self) ==
    LET my_op == p_op[self]
        my_l  == p_l[self]
        my_r  == p_r[self]
        my_new == p_new[self]
        my_val == p_val[self]
    IN
    /\ pc[self] = "PushCommit"
    /\ \/ /\ my_op = "pushL"
          /\ left = my_l
          /\ IF my_l = Nil THEN /\ right = Nil
                                /\ left'  = my_new
                                /\ right' = my_new
                                /\ memory' = [memory EXCEPT ![my_new] = [val |-> my_val, left |-> Nil, right |-> Nil]]
                           ELSE /\ my_l /= Nil /\ memory[my_l].left = Nil
                                /\ left' = my_new
                                /\ memory' = [memory EXCEPT ![my_new] = [val |-> my_val, left |-> Nil, right |-> my_l],
                                                          ![my_l].left = my_new]
                                /\ UNCHANGED right
       \/ /\ my_op = "pushR"
          /\ right = my_r
          /\ IF my_r = Nil THEN /\ left = Nil
                                /\ left'  = my_new
                                /\ right' = my_new
                                /\ memory' = [memory EXCEPT ![my_new] = [val |-> my_val, left |-> Nil, right |-> Nil]]
                           ELSE /\ my_r /= Nil /\ memory[my_r].right = Nil
                                /\ right' = my_new
                                /\ memory' = [memory EXCEPT ![my_new] = [val |-> my_val, left |-> my_r, right |-> Nil],
                                                           ![my_r].right = my_new]
                                /\ UNCHANGED left
    /\ valBag' = [valBag EXCEPT ![my_val] = valBag[my_val] + 1]
    /\ pc' = [pc EXCEPT ![self] = "T1"]
    /\ UNCHANGED << freelist, p_op, p_val, p_l, p_r, p_new, p_node, p_next, p_res >>

\* If commit fails, retry by re-reading.
PushRetry(self) ==
    /\ pc[self] = "PushCommit"
    /\ \/ (p_op[self] = "pushL" /\ left /= p_l[self])
       \/ (p_op[self] = "pushR" /\ right /= p_r[self])
    /\ pc' = [pc EXCEPT ![self] = "PushRead"]
    /\ UNCHANGED << memory, left, right, freelist, valBag, p_op, p_val, 
                    p_l, p_r, p_new, p_node, p_next, p_res >>

\* Pop operations read the global state.
PopRead(self) ==
    /\ pc[self] = "PopRead"
    /\ p_l' = [p_l EXCEPT ![self] = left]
    /\ p_r' = [p_r EXCEPT ![self] = right]
    /\ pc' = [pc EXCEPT ![self] = "PopCommit"]
    /\ UNCHANGED << memory, left, right, freelist, valBag, p_op, p_val,
                    p_new, p_node, p_next, p_res >>

\* Pop operations attempt to commit their changes.
PopCommit(self) ==
    LET my_op == p_op[self]
        my_l  == p_l[self]
        my_r  == p_r[self]
    IN
    /\ pc[self] = "PopCommit"
    /\ \/ /\ my_op = "popL"
          /\ left = my_l
          /\ IF my_l = Nil THEN /\ p_res' = [p_res EXCEPT ![self] = "Empty"]
                                 /\ pc' = [pc EXCEPT ![self] = "T1"]
                                 /\ UNCHANGED << memory, left, right, freelist, valBag >>
                           ELSE LET node_val = memory[my_l].val
                                    next_l = memory[my_l].right
                                IN /\ p_res' = [p_res EXCEPT ![self] = node_val]
                                   /\ freelist' = Append(freelist, my_l)
                                   /\ valBag' = [valBag EXCEPT ![node_val] = valBag[node_val] - 1]
                                   /\ IF my_l = my_r THEN /\ left'  = Nil
                                                          /\ right' = Nil
                                                          /\ UNCHANGED memory
                                                    ELSE /\ left' = next_l
                                                         /\ memory' = [memory EXCEPT ![next_l].left = Nil]
                                                         /\ UNCHANGED right
                                   /\ pc' = [pc EXCEPT ![self] = "T1"]
       \/ /\ my_op = "popR"
          /\ right = my_r
          /\ IF my_r = Nil THEN /\ p_res' = [p_res EXCEPT ![self] = "Empty"]
                                 /\ pc' = [pc EXCEPT ![self] = "T1"]
                                 /\ UNCHANGED << memory, left, right, freelist, valBag >>
                           ELSE LET node_val = memory[my_r].val
                                    next_r = memory[my_r].left
                                IN /\ p_res' = [p_res EXCEPT ![self] = node_val]
                                   /\ freelist' = Append(freelist, my_r)
                                   /\ valBag' = [valBag EXCEPT ![node_val] = valBag[node_val] - 1]
                                   /\ IF my_l = my_r THEN /\ left'  = Nil
                                                          /\ right' = Nil
                                                          /\ UNCHANGED memory
                                                    ELSE /\ right' = next_r
                                                         /\ memory' = [memory EXCEPT ![next_r].right = Nil]
                                                         /\ UNCHANGED left
                                   /\ pc' = [pc EXCEPT ![self] = "T1"]
    /\ UNCHANGED << p_op, p_val, p_l, p_r, p_new, p_node, p_next >>

\* If commit fails, retry by re-reading.
PopRetry(self) ==
    /\ pc[self] = "PopCommit"
    /\ \/ (p_op[self] = "popL" /\ left /= p_l[self])
       \/ (p_op[self] = "popR" /\ right /= p_r[self])
    /\ pc' = [pc EXCEPT ![self] = "PopRead"]
    /\ UNCHANGED << memory, left, right, freelist, valBag, p_op, p_val,
                    p_l, p_r, p_new, p_node, p_next, p_res >>

\* A process action is a disjunction of all its possible steps.
Proc(self) ==
    \/ Test(self)
    \/ Alloc(self)
    \/ PushRead(self)
    \/ PushCommit(self)
    \/ PushRetry(self)
    \/ PopRead(self)
    \/ PopCommit(self)
    \/ PopRetry(self)

Next == \E self \in Procs : Proc(self)

-------------------------------- Properties --------------------------------

Fairness == \A self \in Procs : WF_vars(Proc(self))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Liveness property: every process eventually returns to its idle state.
Liveness == \A self \in Procs : []<>(pc[self] = "T1")

=============================================================================