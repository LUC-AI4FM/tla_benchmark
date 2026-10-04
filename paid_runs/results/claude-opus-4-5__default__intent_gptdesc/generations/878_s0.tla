---------------------------- MODULE SpanningTree ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS 
    Nodes,          \* Finite set of nodes
    Edges,          \* Set of undirected edges (pairs of nodes)
    Root,           \* Distinguished root node
    Bound           \* Numeric bound >= |Nodes|

VARIABLES
    parent,         \* parent[n] = parent pointer for node n
    dist,           \* dist[n] = distance from root for node n
    msgs            \* msgs[n] = multiset/set of messages in transit to node n

vars == <<parent, dist, msgs>>

-----------------------------------------------------------------------------
(* Helper definitions *)

\* Neighbors of a node n in the undirected graph
Neighbors(n) == {m \in Nodes : {n, m} \in Edges}

\* Nodes reachable from root via edges
Reachable == 
    LET RECURSIVE ReachableFrom(_)
        ReachableFrom(S) == 
            LET NewNodes == S \cup UNION {Neighbors(n) : n \in S}
            IN IF NewNodes = S THEN S ELSE ReachableFrom(NewNodes)
    IN ReachableFrom({Root})

\* Check if the system has quiesced (no more steps enabled)
Quiesced ==
    /\ \A n \in Nodes : msgs[n] = {}
    /\ \A n \in Nodes \ {Root} :
        LET neighborDists == {dist[m] : m \in Neighbors(n)}
        IN neighborDists = {} \/ dist[n] <= 1 + Min(neighborDists)
           WHERE Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Minimum of a non-empty set
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ parent \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..Bound]
    /\ msgs \in [Nodes -> SUBSET (Nodes \X (0..Bound))]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ parent = [n \in Nodes |-> n]         \* Initially every node points to itself
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Bound]
    /\ msgs = [n \in Nodes |-> 
                IF n \in Neighbors(Root) 
                THEN {<<Root, 0>>}          \* Root announces distance 0 to neighbors
                ELSE {}]

-----------------------------------------------------------------------------
(* Actions *)

\* A node receives a message and potentially updates its state
ReceiveMessage(n) ==
    /\ n # Root                             \* Root doesn't process incoming messages
    /\ msgs[n] # {}                         \* There is a message to process
    /\ \E msg \in msgs[n] :
        LET sender == msg[1]
            senderDist == msg[2]
            newDist == senderDist + 1
        IN
            /\ msgs' = [msgs EXCEPT ![n] = @ \ {msg}]
            /\ IF newDist < dist[n]
               THEN 
                    /\ dist' = [dist EXCEPT ![n] = newDist]
                    /\ parent' = [parent EXCEPT ![n] = sender]
                    \* Send new distance to all neighbors
                    /\ msgs' = [m \in Nodes |-> 
                                IF m \in Neighbors(n) 
                                THEN msgs[m] \cup {<<n, newDist>>} \ (IF m = n THEN {msg} ELSE {})
                                ELSE IF m = n THEN msgs[m] \ {msg} ELSE msgs[m]]
               ELSE
                    /\ dist' = dist
                    /\ parent' = parent
                    /\ msgs' = [msgs EXCEPT ![n] = @ \ {msg}]

\* Simplified receive that handles message removal and state update atomically
Receive(n) ==
    /\ n # Root
    /\ msgs[n] # {}
    /\ \E msg \in msgs[n] :
        LET sender == msg[1]
            senderDist == msg[2]
            newDist == senderDist + 1
        IN
            IF newDist < dist[n]
            THEN 
                /\ dist' = [dist EXCEPT ![n] = newDist]
                /\ parent' = [parent EXCEPT ![n] = sender]
                /\ msgs' = [m \in Nodes |-> 
                            IF m = n THEN msgs[m] \ {msg}
                            ELSE IF m \in Neighbors(n) THEN msgs[m] \cup {<<n, newDist>>}
                            ELSE msgs[m]]
            ELSE
                /\ dist' = dist
                /\ parent' = parent
                /\ msgs' = [msgs EXCEPT ![n] = @ \ {msg}]

-----------------------------------------------------------------------------
(* Next state relation *)

Next == \E n \in Nodes : Receive(n)

-----------------------------------------------------------------------------
(* Fairness *)

Fairness == \A n \in Nodes : WF_vars(Receive(n))

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Properties *)

\* When quiesced, reachable nodes have correct distance (hop count from root)
\* and parent pointers form a spanning tree to root
\* Unreachable nodes point to themselves with distance = Bound

CorrectDistance(n) ==
    IF n = Root THEN dist[n] = 0
    ELSE IF n \in Reachable 
         THEN dist[n] = dist[parent[n]] + 1
         ELSE dist[n] = Bound

CorrectParent(n) ==
    IF n = Root THEN parent[n] = Root
    ELSE IF n \in Reachable
         THEN parent[n] \in Neighbors(n)
         ELSE parent[n] = n

\* Following parent pointers from reachable node leads to root
ReachesRoot(n) ==
    IF n \notin Reachable THEN TRUE
    ELSE 
        LET RECURSIVE PathToRoot(_,_)
            PathToRoot(m, visited) ==
                IF m = Root THEN TRUE
                ELSE IF m \in visited THEN FALSE
                ELSE PathToRoot(parent[m], visited \cup {m})
        IN PathToRoot(n, {})

\* Safety: upon quiescence, the spanning tree is correct
SafetyInvariant ==
    (Quiesced') => 
        /\ \A n \in Nodes : CorrectDistance(n)'
        /\ \A n \in Nodes : CorrectParent(n)'
        /\ \A n \in Nodes : ReachesRoot(n)'

\* Stable safety property that can be checked as invariant
\* Distance is always bounded and consistent with known information
DistanceBounded == \A n \in Nodes : dist[n] <= Bound

ParentConsistent == 
    \A n \in Nodes :
        /\ (n = Root) => (parent[n] = Root /\ dist[n] = 0)
        /\ (parent[n] # n /\ n # Root) => parent[n] \in Neighbors(n)
        /\ (dist[n] < Bound /\ n # Root) => parent[n] \in Neighbors(n)

Safety == DistanceBounded /\ ParentConsistent

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* The system eventually quiesces
EventuallyQuiesced == <>[](\A n \in Nodes : msgs[n] = {})

\* Upon quiescence, postcondition holds
PostConditionOnQuiescence ==
    [](\A n \in Nodes : msgs[n] = {}) => 
        /\ \A n \in Nodes : CorrectDistance(n)
        /\ \A n \in Nodes : CorrectParent(n)
        /\ \A n \in Reachable : ReachesRoot(n)

\* Combined termination property
Termination == 
    <>(\A n \in Nodes : 
        /\ msgs[n] = {}
        /\ CorrectDistance(n)
        /\ CorrectParent(n))

Liveness == EventuallyQuiesced /\ Termination

=============================================================================