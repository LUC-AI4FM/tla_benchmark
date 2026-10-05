---------------------------- MODULE Deque ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    defaultInitValue,
    Val,
    Clients,
    Nodes,
    SENTINEL_LEFT,
    SENTINEL_RIGHT

VARIABLES
    deque_head,
    deque_tail,
    node_value,
    node_left,
    node_right,
    node_allocated,
    node_reachable,
    client_state,
    client_op,
    client_arg,
    client_result,
    abstract_deque,
    linearization_point

vars == <<deque_head, deque_tail, node_value, node_left, node_right,
          node_allocated, node_reachable, client_state, client_op,
          client_arg, client_result, abstract_deque, linearization_point>>

NullNode == CHOOSE n : n \notin Nodes
NullVal == CHOOSE v : v \notin Val

ClientStates == {"idle", "push_left_alloc", "push_left_link", "push_left_cas",
                 "push_right_alloc", "push_right_link", "push_right_cas",
                 "pop_left_read", "pop_left_cas",
                 "pop_right_read", "pop_right_cas", "done"}

Operations == {"none", "pushLeft", "pushRight", "popLeft", "popRight"}

Results == {"ok", "empty", "full"} \cup Val

TypeInvariant ==
    /\ deque_head \in Nodes \cup {NullNode}
    /\ deque_tail \in Nodes \cup {NullNode}
    /\ node_value \in [Nodes -> Val \cup {NullVal}]
    /\ node_left \in [Nodes -> Nodes \cup {NullNode}]
    /\ node_right \in [Nodes -> Nodes \cup {NullNode}]
    /\ node_allocated \in [Nodes -> BOOLEAN]
    /\ node_reachable \in [Nodes -> BOOLEAN]
    /\ client_state \in [Clients -> ClientStates]
    /\ client_op \in [Clients -> Operations]
    /\ client_arg \in [Clients -> Val \cup {NullVal} \cup Nodes \cup {NullNode}]
    /\ client_result \in [Clients -> Results \cup {NullVal}]
    /\ abstract_deque \in Seq(Val)
    /\ linearization_point \in Nat

FreeNodes == {n \in Nodes : ~node_allocated[n]}

ReachableFrom(start) ==
    LET RECURSIVE Reach(_)
        Reach(visited) ==
            LET frontier == {n \in Nodes : 
                /\ n \notin visited
                /\ \E v \in visited:
                    \/ node_left[v] = n
                    \/ node_right[v] = n}
            IN IF frontier = {} THEN visited
               ELSE Reach(visited \cup frontier)
    IN IF start = NullNode THEN {}
       ELSE Reach({start})

AllReachable ==
    LET fromHead == ReachableFrom(deque_head)
        fromTail == ReachableFrom(deque_tail)
    IN fromHead \cup fromTail

Init ==
    /\ deque_head = SENTINEL_LEFT
    /\ deque_tail = SENTINEL_RIGHT
    /\ node_value = [n \in Nodes |-> 
        IF n = SENTINEL_LEFT \/ n = SENTINEL_RIGHT THEN NullVal ELSE NullVal]
    /\ node_left = [n \in Nodes |->
        IF n = SENTINEL_RIGHT THEN SENTINEL_LEFT ELSE NullNode]
    /\ node_right = [n \in Nodes |->
        IF n = SENTINEL_LEFT THEN SENTINEL_RIGHT ELSE NullNode]
    /\ node_allocated = [n \in Nodes |->
        IF n = SENTINEL_LEFT \/ n = SENTINEL_RIGHT THEN TRUE ELSE FALSE]
    /\ node_reachable = [n \in Nodes |->
        IF n = SENTINEL_LEFT \/ n = SENTINEL_RIGHT THEN TRUE ELSE FALSE]
    /\ client_state = [c \in Clients |-> "idle"]
    /\ client_op = [c \in Clients |-> "none"]
    /\ client_arg = [c \in Clients |-> NullVal]
    /\ client_result = [c \in Clients |-> NullVal]
    /\ abstract_deque = <<>>
    /\ linearization_point = 0

AllocateNode(c, n) ==
    /\ n \in FreeNodes
    /\ node_allocated' = [node_allocated EXCEPT ![n] = TRUE]
    /\ node_reachable' = [node_reachable EXCEPT ![n] = TRUE]
    /\ client_arg' = [client_arg EXCEPT ![c] = n]

AllocFailed(c) ==
    /\ FreeNodes = {}
    /\ client_result' = [client_result EXCEPT ![c] = "full"]
    /\ client_state' = [client_state EXCEPT ![c] = "done"]
    /\ UNCHANGED <<node_allocated, node_reachable, client_arg>>

StartPushLeft(c, v) ==
    /\ client_state[c] = "idle"
    /\ client_op' = [client_op EXCEPT ![c] = "pushLeft"]
    /\ client_state' = [client_state EXCEPT ![c] = "push_left_alloc"]
    /\ client_arg' = [client_arg EXCEPT ![c] = v]
    /\ client_result' = [client_result EXCEPT ![c] = NullVal]
    /\ UNCHANGED <<deque_head, deque_tail, node_value, node_left, node_right,
                   node_allocated, node_reachable, abstract_deque, linearization_point>>

PushLeftAlloc(c) ==
    /\ client_state[c] = "push_left_alloc"
    /\ \/ \E n \in FreeNodes:
          /\ AllocateNode(c, n)
          /\ node_value' = [node_value EXCEPT ![n] = client_arg[c]]
          /\ client_state' = [client_state EXCEPT ![c] = "push_left_link"]
          /\ UNCHANGED <<deque_head, deque_tail, node_left, node_right,
                         client_op, client_result, abstract_deque, linearization_point>>
       \/ AllocFailed(c) /\
          UNCHANGED <<deque_head, deque_tail, node_value, node_left, node_right,
                      client_op, abstract_deque, linearization_point>>

PushLeftCAS(c) ==
    /\ client_state[c] = "push_left_link"
    /\ LET n == client_arg[c]
           oldHead == deque_head
           nextNode == node_right[oldHead]
       IN /\ node_left' = [node_left EXCEPT ![n] = oldHead, ![nextNode] = n]
          /\ node_right' = [node_right EXCEPT ![n] = nextNode, ![oldHead] = n]
          /\ deque_head' = deque_head
          /\ abstract_deque' = <<node_value[n]>> \o abstract_deque
          /\ linearization_point' = linearization_point + 1
          /\ client_result' = [client_result EXCEPT ![c] = "ok"]
          /\ client_state' = [client_state EXCEPT ![c] = "done"]
    /\ UNCHANGED <<deque_tail, node_value, node_allocated, node_reachable,
                   client_op, client_arg>>

StartPushRight(c, v) ==
    /\ client_state[c] = "idle"
    /\ client_op' = [client_op EXCEPT ![c] = "pushRight"]
    /\ client_state' = [client_state EXCEPT ![c] = "push_right_alloc"]
    /\ client_arg' = [client_arg EXCEPT ![c] = v]
    /\ client_result' = [client_result EXCEPT ![c] = NullVal]
    /\ UNCHANGED <<deque_head, deque_tail, node_value, node_left, node_right,
                   node_allocated, node_reachable, abstract_deque, linearization_point>>

PushRightAlloc(c) ==
    /\ client_state[c] = "push_right_alloc"
    /\ \/ \E n \in FreeNodes:
          /\ AllocateNode(c, n)
          /\ node_value' = [node_value EXCEPT ![n] = client_arg[c]]
          /\ client_state' = [client_state EXCEPT ![c] = "push_right_link"]
          /\ UNCHANGED <<deque_head, deque_tail, node_left, node_right,
                         client_op, client_result, abstract_deque, linearization_point>>
       \/ AllocFailed(c) /\
          UNCHANGED <<deque_head, deque_tail, node_value, node_left, node_right,
                      client_op, abstract_deque, linearization_point>>

PushRightCAS(c) ==
    /\ client_state[c] = "push_right_link"
    /\ LET n == client_arg[c]
           oldTail == deque_tail
           prevNode == node_left[oldTail]
       IN /\ node_right' = [node_right EXCEPT ![n] = oldTail, ![prevNode] = n]
          /\ node_left' = [node_left EXCEPT ![n] = prevNode, ![oldTail] = n]
          /\ deque_tail' = deque_tail
          /\ abstract_deque' = abstract_deque \o <<node_value[n]>>
          /\ linearization_point' = linearization_point + 1
          /\ client_result' = [client_result EXCEPT ![c] = "ok"]
          /\ client_state' = [client_state EXCEPT ![c] = "done"]
    /\ UNCHANGED <<deque_head, node_value, node_allocated, node_reachable,
                   client_op, client_arg>>

StartPopLeft(c) ==
    /\ client_state[c] = "idle"
    /\ client_op' = [client_op EXCEPT ![c] = "popLeft"]
    /\ client_state' = [client_state EXCEPT ![c] = "pop_left_read"]
    /\ client_result' = [client_result EXCEPT ![c] = NullVal]
    /\ UNCHANGED <<deque_head, deque_tail, node_value, node_left, node_right,
                   node_allocated, node_reachable, client_arg, abstract_deque, linearization_point>>

PopLeftCAS(c) ==
    /\ client_state[c] = "pop_left_read"
    /\ LET firstNode == node_right[deque_head]
       IN IF firstNode = deque_tail
          THEN /\ client_result' = [client_result EXCEPT ![c] = "empty"]
               /\ client_state' = [client_state EXCEPT ![c] = "done"]
               /\ UNCHANGED <<deque_head, deque_tail, node_value, node_left, node_right,
                              node_allocated, node_reachable, client_op, client_arg,
                              abstract_deque, linearization_point>>
          ELSE LET v == node_value[firstNode]
                   nextNode == node_right[firstNode]
               IN /\ node_right' = [node_right EXCEPT ![deque_head] = nextNode]
                  /\ node_left' = [node_left EXCEPT ![nextNode] = deque_head]
                  /\ node_reachable' = [node_reachable EXCEPT ![firstNode] = FALSE]
                  /\ abstract_deque' = Tail(abstract_deque)
                  /\ linearization_point' = linearization_point + 1
                  /\ client_result' = [client_result EXCEPT ![c] = v]
                  /\ client_state' = [client_state EXCEPT ![c] = "done"]
                  /\ UNCHANGED <<deque_head, deque_tail, node_value, node_allocated,
                                 client_op, client_arg>>

StartPopRight(c) ==
    /\ client_state[c] = "idle"
    /\ client_op' = [client_op EXCEPT ![c] = "popRight"]
    /\ client_state' = [client_state EXCEPT ![c] = "pop_right_read"]
    /\ client_result' = [client_result EXCEPT ![c] = NullVal]
    /\ UNCHANGED <<deque_head, deque_tail, node_value, node_left, node_right,
                   node_allocated, node_reachable, client_arg, abstract_deque, linearization_point>>

PopRightCAS(c) ==
    /\ client_state[c] = "pop_right_read"
    /\ LET lastNode == node_left[deque_tail]
       IN IF lastNode = deque_head
          THEN /\ client_result' = [client_result EXCEPT ![c] = "empty"]
               /\ client_state' = [client_state EXCEPT ![c] = "done"]
               /\ UNCHANGED <<deque_head, deque_tail, node_value, node_left, node_right,
                              node_allocated, node_reachable, client_op, client_arg,
                              abstract_deque, linearization_point>>
          ELSE LET v == node_value[lastNode]
                   prevNode == node_left[lastNode]
               IN /\ node_left' = [node_left EXCEPT ![deque_tail] = prevNode]
                  /\ node_right' = [node_right EXCEPT ![prevNode] = deque_tail]
                  /\ node_reachable' = [node_reachable EXCEPT ![lastNode] = FALSE]
                  /\ abstract_deque' = SubSeq(abstract_deque, 1, Len(abstract_deque) - 1)
                  /\ linearization_point' = linearization_point + 1
                  /\ client_result' = [client_result EXCEPT ![c] = v]
                  /\ client_state' = [client_state EXCEPT ![c] = "done"]
                  /\ UNCHANGED <<deque_head, deque_tail, node_value, node_allocated,
                                 client_op, client_arg>>

ClientDone(c) ==
    /\ client_state[c] = "done"
    /\ client_state' = [client_state EXCEPT ![c] = "idle"]
    /\ client_op' = [client_op EXCEPT ![c] = "none"]
    /\ client_arg' = [client_arg EXCEPT ![c] = NullVal]
    /\ client_result' = [client_result EXCEPT ![c] = NullVal]
    /\ UNCHANGED <<deque_head, deque_tail, node_value, node_left, node_right,
                   node_allocated, node_reachable, abstract_deque, linearization_point>>

GarbageCollect ==
    /\ \E n \in Nodes:
        /\ node_allocated[n]
        /\ ~node_reachable[n]
        /\ n \notin AllReachable
        /\ node_allocated' = [node_allocated EXCEPT ![n] = FALSE]
        /\ node_value' = [node_value EXCEPT ![n] = NullVal]
        /\ node_left' = [node_left EXCEPT ![n] = NullNode]
        /\ node_right' = [node_right EXCEPT ![n] = NullNode]
    /\ UNCHANGED <<deque_head, deque_tail, node_reachable, client_state,
                   client_op, client_arg, client_result, abstract_deque, linearization_point>>

ClientAction(c) ==
    \/ \E v \in Val: StartPushLeft(c, v)
    \/ \E v \in Val: StartPushRight(c, v)
    \/ StartPopLeft(c)
    \/ StartPopRight(c)
    \/ PushLeftAlloc(c)
    \/ PushLeftCAS(c)
    \/ PushRightAlloc(c)
    \/ PushRightCAS(c)
    \/ PopLeftCAS(c)
    \/ PopRightCAS(c)
    \/ ClientDone(c)

Next ==
    \/ \E c \in Clients: ClientAction(c)
    \/ GarbageCollect

Fairness ==
    /\ \A c \in Clients: WF_vars(ClientAction(c))

Spec == Init /\ [][Next]_vars /\ Fairness

StructuralIntegrity ==
    /\ deque_head = SENTINEL_LEFT
    /\ deque_tail = SENTINEL_RIGHT
    /\ node_right[SENTINEL_LEFT] \in Nodes
    /\ node_left[SENTINEL_RIGHT] \in Nodes

MemorySafety ==
    \A n \in Nodes:
        ~node_allocated[n] => n \notin AllReachable

NoValueDuplication ==
    LET activeNodes == {n \in Nodes : 
            /\ node_allocated[n]
            /\ node_reachable[n]
            /\ n /= SENTINEL_LEFT
            /\ n /= SENTINEL_RIGHT}
        values == {node_value[n] : n \in activeNodes}
    IN Cardinality(values) = Cardinality(activeNodes) \/ activeNodes = {}

Safety ==
    /\ TypeInvariant
    /\ StructuralIntegrity
    /\ MemorySafety

Progress ==
    \A c \in Clients:
        client_state[c] /= "idle" ~> client_state[c] = "done"

=============================================================================