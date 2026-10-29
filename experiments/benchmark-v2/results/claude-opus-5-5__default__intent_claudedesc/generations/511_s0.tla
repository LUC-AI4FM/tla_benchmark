---------------------------- MODULE DistributedBFS ----------------------------
(***************************************************************************)
(* Distributed construction of a breadth-first search spanning tree.       *)
(* A designated Root starts the algorithm. Each node keeps its best known  *)
(* depth (distance from Root) and a parent pointer. Messages travel over   *)
(* asynchronous FIFO channels between neighbours and carry the sender's    *)
(* current depth. When a node receives a message with depth d and          *)
(* d + 1 < depth, it adopts depth d + 1 and the sender as its parent. It    *)
(* then sends its new depth to all of its neighbours. Since depths only    *)
(* decrease and are bounded, the algorithm terminates. When it terminates, *)
(* every depth equals the true graph distance from Root.                   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,      \* finite set of nodes
    Root,       \* distinguished root node
    Nbrs        \* Nbrs[n] : set of neighbours of node n (fixed topology)

ASSUME RootInNodes   == Root \in Nodes
ASSUME NbrsType      == Nbrs \in [Nodes -> SUBSET Nodes]
ASSUME NoSelfLoops   == \A n \in Nodes : n \notin Nbrs[n]
ASSUME Symmetric     == \A n, m \in Nodes : m \in Nbrs[n] <=> n \in Nbrs[m]

(* "Infinity": strictly larger than any real distance in a graph of N nodes *)
Inf == Cardinality(Nodes)

(* Directed channels between neighbouring nodes *)
Edges == { e \in Nodes \X Nodes : e[2] \in Nbrs[e[1]] }

(* Nodes reachable from Root in at most k hops *)
RECURSIVE ReachWithin(_)
ReachWithin(k) ==
    IF k = 0 THEN {Root}
    ELSE LET R == ReachWithin(k - 1)
         IN  R \cup UNION { Nbrs[x] : x \in R }

ASSUME Connected == ReachWithin(Inf) = Nodes

(* True shortest-path distance from Root *)
Dist(n) == CHOOSE k \in 0..(Inf - 1) :
               /\ n \in ReachWithin(k)
               /\ (k = 0 \/ n \notin ReachWithin(k - 1))

VARIABLES
    depth,      \* depth[n] : current known distance of n from Root (Inf = unknown)
    parent,     \* parent[n] : current parent of n (n itself if none yet; Root for Root)
    chan,       \* chan[<<n,m>>] : FIFO queue of depth values sent from n to m
    started     \* TRUE once the root has initiated the algorithm

vars == <<depth, parent, chan, started>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ depth   \in [Nodes -> 0..Inf]
    /\ parent  \in [Nodes -> Nodes]
    /\ chan    \in [Edges -> Seq(0..(Inf - 1))]
    /\ started \in BOOLEAN

Init ==
    /\ depth   = [n \in Nodes |-> IF n = Root THEN 0 ELSE Inf]
    /\ parent  = [n \in Nodes |-> n]
    /\ chan    = [e \in Edges |-> << >>]
    /\ started = FALSE

(* The root initiates the algorithm by sending its depth to all neighbours *)
RootStart ==
    /\ ~started
    /\ started' = TRUE
    /\ chan' = [e \in Edges |->
                  IF e[1] = Root THEN Append(chan[e], 0) ELSE chan[e]]
    /\ UNCHANGED <<depth, parent>>

(* Node m receives the message at the head of the channel from n *)
Receive(n, m) ==
    /\ <<n, m>> \in Edges
    /\ chan[<<n, m>>] # << >>
    /\ LET d     == Head(chan[<<n, m>>])
           rest  == [chan EXCEPT ![<<n, m>>] = Tail(@)]
       IN  IF d + 1 < depth[m]
             THEN /\ depth'  = [depth  EXCEPT ![m] = d + 1]
                  /\ parent' = [parent EXCEPT ![m] = n]
                  /\ chan'   = [e \in Edges |->
                                  IF e[1] = m THEN Append(rest[e], d + 1)
                                              ELSE rest[e]]
             ELSE /\ chan' = rest
                  /\ UNCHANGED <<depth, parent>>
    /\ UNCHANGED started

Next ==
    \/ RootStart
    \/ \E e \in Edges : Receive(e[1], e[2])

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* All message queues are empty *)
QueuesEmpty == \A e \in Edges : chan[e] = << >>

Terminated == started /\ QueuesEmpty

(* Message validity: every message in transit carries a depth that is not *)
(* smaller than the sender's current depth. Depths only decrease, so      *)
(* in-flight messages are never "fresher" than the current state, and     *)
(* each depth corresponds to an actual path from Root.                    *)
MsgValid ==
    \A e \in Edges :
        \A i \in 1..Len(chan[e]) :
            /\ chan[e][i] >= depth[e[1]]
            /\ chan[e][i] >= Dist(e[1])

(* Depths never underestimate the true distance; parent pointers stay *)
(* consistent with the graph.                                         *)
DepthSound ==
    /\ depth[Root] = 0
    /\ \A n \in Nodes :
         /\ depth[n] >= Dist(n)
         /\ (n # Root /\ depth[n] < Inf) => parent[n] \in Nbrs[n]

(* BFS correctness upon termination *)
BFSCorrect ==
    Terminated =>
        /\ \A n \in Nodes : depth[n] = Dist(n)
        /\ parent[Root] = Root
        /\ \A n \in Nodes \ {Root} :
              /\ parent[n] \in Nbrs[n]
              /\ depth[n] = depth[parent[n]] + 1

(* Liveness: the algorithm eventually terminates with all queues empty *)
Termination == <>[](Terminated)

THEOREM Spec => [](TypeOK /\ MsgValid /\ DepthSound /\ BFSCorrect)
THEOREM Spec => Termination
=============================================================================