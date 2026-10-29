---------------------------- MODULE MCSession10set ----------------------------
(***************************************************************************)
(* Model-checking configuration for a breadth-first / shortest-path        *)
(* spanning tree construction by message passing over an undirected graph. *)
(* The base algorithm (in the style of Session10set) is included directly, *)
(* so this module is self-contained.                                       *)
(*                                                                         *)
(* Each node keeps its current depth estimate and its parent in the tree.  *)
(* Each directed channel <<m, n>> between adjacent nodes holds a SET of    *)
(* depth values that m has proposed to n.                                  *)
(*                                                                         *)
(* Deadlock checking should be disabled in the configuration: once all     *)
(* channels are empty the algorithm stops in a quiescent state.            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,     \* set of graph nodes
          Root,      \* the distinguished root node
          Edges,     \* set of undirected edges, each a 2-element set {a, b}
          MaxNodes   \* bound on the number of nodes, used as "infinity"

(***************************************************************************)
(* Concrete topology for model checking: 6 nodes and 6 edges.              *)
(* In the TLC config, use  Nodes <- MCNodes, Root <- MCRoot,               *)
(* Edges <- MCEdges, and MaxNodes <- MCMaxNodes.                           *)
(***************************************************************************)
MCNodes    == {1, 2, 3, 4, 5, 6}
MCRoot     == 1
MCEdges    == { {1, 2}, {1, 3}, {2, 4}, {3, 4}, {4, 5}, {5, 6} }
MCMaxNodes == 6

ASSUME /\ Root \in Nodes
       /\ Edges \subseteq SUBSET Nodes
       /\ \A e \in Edges : Cardinality(e) = 2
       /\ MaxNodes \in Nat
       /\ Cardinality(Nodes) <= MaxNodes

VARIABLES depth,   \* depth[n] : current depth estimate of node n
          parent,  \* parent[n] : current parent of n in the spanning tree
          msgs     \* msgs[<<m, n>>] : set of depths sent from m to n

vars == <<depth, parent, msgs>>

-----------------------------------------------------------------------------
Nbrs(n)  == { m \in Nodes : {m, n} \in Edges }

Channels == { <<m, n>> \in Nodes \X Nodes : {m, n} \in Edges }

Infinity == MaxNodes

(***************************************************************************)
(* True shortest-path distance from the root, computed by BFS levels.      *)
(***************************************************************************)
RECURSIVE Reach(_)
Reach(k) == IF k = 0 THEN {Root}
            ELSE LET R == Reach(k - 1)
                 IN  R \cup { n \in Nodes : \E m \in R : {m, n} \in Edges }

Dist(n) == IF n \in Reach(MaxNodes)
             THEN CHOOSE k \in 0..MaxNodes :
                     /\ n \in Reach(k)
                     /\ (k = 0 \/ n \notin Reach(k - 1))
             ELSE Infinity

(***************************************************************************)
(* Length of the path from n to the root following parent pointers.       *)
(* Bounded by a fuel argument; MaxNodes + 1 signals "no path to root".     *)
(***************************************************************************)
RECURSIVE PL(_, _)
PL(n, k) == IF n = Root THEN 0
            ELSE IF k = 0 THEN MaxNodes + 1
            ELSE 1 + PL(parent[n], k - 1)

PathLen(n) == PL(n, MaxNodes)

-----------------------------------------------------------------------------
TypeOK ==
  /\ depth  \in [Nodes -> 0..MaxNodes]
  /\ parent \in [Nodes -> Nodes]
  /\ msgs   \in [Channels -> SUBSET (1..MaxNodes)]
  \* A queued depth on <<m, n>> is never smaller than the sender's depth + 1,
  \* because depths only decrease after a value has been sent.
  /\ \A c \in Channels : \A d \in msgs[c] : d >= depth[c[1]] + 1

Init ==
  /\ depth  = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]
  /\ parent = [n \in Nodes |-> n]
  /\ msgs   = [c \in Channels |-> IF c[1] = Root THEN {1} ELSE {}]

(***************************************************************************)
(* Node n receives depth d from neighbour m. If d improves on n's current  *)
(* depth, n adopts it, sets m as its parent, and proposes d + 1 to all of  *)
(* its other neighbours.                                                   *)
(***************************************************************************)
Receive(m, n) ==
  /\ <<m, n>> \in Channels
  /\ msgs[<<m, n>>] # {}
  /\ \E d \in msgs[<<m, n>>] :
       IF d < depth[n]
         THEN /\ depth'  = [depth  EXCEPT ![n] = d]
              /\ parent' = [parent EXCEPT ![n] = m]
              /\ msgs' = [c \in Channels |->
                            IF c = <<m, n>>
                              THEN msgs[c] \ {d}
                            ELSE IF c[1] = n /\ c[2] # m /\ d + 1 < MaxNodes
                              THEN msgs[c] \cup {d + 1}
                            ELSE msgs[c]]
         ELSE /\ msgs' = [msgs EXCEPT ![<<m, n>>] = @ \ {d}]
              /\ UNCHANGED <<depth, parent>>

Next == \E m, n \in Nodes : Receive(m, n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
Terminated == \A c \in Channels : msgs[c] = {}

(* Safety: once all queues are empty, parent paths have shortest length. *)
DepthCorrect == Terminated => \A n \in Nodes : PathLen(n) = Dist(n)

(* Liveness: all message queues eventually become empty. *)
Termination == <>Terminated

THEOREM Spec => []TypeOK /\ []DepthCorrect /\ Termination
=============================================================================