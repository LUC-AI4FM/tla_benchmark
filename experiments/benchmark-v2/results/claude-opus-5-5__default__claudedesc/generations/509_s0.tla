------------------------------- MODULE MCSession10 -------------------------------
(***************************************************************************)
(* Model-checking configuration and correctness properties for a          *)
(* distributed breadth-first search that computes shortest-path distances *)
(* from a designated root in an undirected graph.                         *)
(*                                                                         *)
(* The base behaviour (Session10) is included inline so that this module  *)
(* is self-contained:                                                      *)
(*   - Each directed edge <<m, n>> of the graph is a FIFO queue from m     *)
(*     to n.                                                               *)
(*   - A message carries the sender's depth at the moment of sending.      *)
(*   - A receiver that learns of a shorter path adopts the sender as its   *)
(*     parent, lowers its depth, and notifies all of its neighbours.       *)
(*                                                                         *)
(* TLC configuration (deadlock checking is disabled because termination   *)
(* with empty queues is the expected final state):                        *)
(*   CONSTANTS Nodes <- MCNodes  Edges <- MCEdges                          *)
(*             root <- MCRoot    MaxNodes <- MCMaxNodes                    *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANTS TypeOK DepthCorrect                                        *)
(*   PROPERTIES Termination                                                *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Edges, root, MaxNodes

VARIABLES depth, parent, msgs

vars == <<depth, parent, msgs>>

(***************************************************************************)
(* Concrete model values: six nodes, six undirected edges, root "r".      *)
(***************************************************************************)
MCNodes    == {"r", "a", "b", "c", "d", "e"}
MCEdges    == { {"r", "a"}, {"r", "b"}, {"a", "c"},
                {"b", "c"}, {"c", "d"}, {"d", "e"} }
MCRoot     == "r"
MCMaxNodes == 6

ASSUME /\ root \in Nodes
       /\ MaxNodes \in Nat
       /\ Cardinality(Nodes) <= MaxNodes
       /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2

(***************************************************************************)
(* Graph helpers.                                                          *)
(***************************************************************************)
Nbrs(n) == { m \in Nodes : {m, n} \in Edges }

Queues == { q \in Nodes \X Nodes : {q[1], q[2]} \in Edges }

\* MaxNodes plays the role of "infinity" for unreached nodes.
Infinity == MaxNodes

(***************************************************************************)
(* Base specification (Session10).                                         *)
(***************************************************************************)
Init ==
  /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE Infinity]
  /\ parent = [n \in Nodes |-> n]
  /\ msgs   = [q \in Queues |-> IF q[1] = root THEN <<0>> ELSE <<>>]

Receive(m, n) ==
  LET q == <<m, n>>
      d == Head(msgs[q])
  IN  /\ msgs[q] # <<>>
      /\ IF d + 1 < depth[n]
           THEN /\ depth'  = [depth  EXCEPT ![n] = d + 1]
                /\ parent' = [parent EXCEPT ![n] = m]
                /\ msgs'   = [r \in Queues |->
                                IF r = q THEN Tail(msgs[q])
                                ELSE IF r[1] = n THEN Append(msgs[r], d + 1)
                                ELSE msgs[r]]
           ELSE /\ msgs' = [msgs EXCEPT ![q] = Tail(msgs[q])]
                /\ UNCHANGED <<depth, parent>>

Next == \E q \in Queues : Receive(q[1], q[2])

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Type invariant.                                                         *)
(***************************************************************************)
TypeOK ==
  /\ depth  \in [Nodes -> 0..MaxNodes]
  /\ parent \in [Nodes -> Nodes]
  /\ DOMAIN msgs = Queues
  /\ \A q \in Queues :
       /\ msgs[q] \in Seq(0..MaxNodes)
       /\ Len(msgs[q]) <= MaxNodes
       \* messages in a queue are strictly decreasing
       /\ \A i \in 1..Len(msgs[q]) : \A j \in 1..Len(msgs[q]) :
            i < j => msgs[q][i] > msgs[q][j]
       \* and bounded below by the sender's current depth
       /\ \A i \in 1..Len(msgs[q]) : msgs[q][i] >= depth[q[1]]

(***************************************************************************)
(* Auxiliary definitions.                                                  *)
(***************************************************************************)
\* Path from n towards the root following parent pointers (bounded length).
RECURSIVE PP(_, _)
PP(n, k) == IF n = root \/ k = 0 THEN <<n>> ELSE <<n>> \o PP(parent[n], k - 1)

PPath(n) == PP(n, MaxNodes)

\* Set of nodes within distance k of s.
RECURSIVE Within(_, _)
Within(s, k) == IF k = 0 THEN {s}
                ELSE LET W == Within(s, k - 1)
                     IN  W \cup { m \in Nodes : \E w \in W : {w, m} \in Edges }

\* True graph distance from s to n (Infinity if unreachable).
DistanceFrom(s, n) ==
  IF n \in Within(s, MaxNodes)
    THEN CHOOSE k \in 0..MaxNodes :
           /\ n \in Within(s, k)
           /\ (k = 0 \/ n \notin Within(s, k - 1))
    ELSE Infinity

Dist(n) == DistanceFrom(root, n)

Terminated == \A q \in Queues : msgs[q] = <<>>

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
\* Upon termination, the parent-pointer path of every node has length equal
\* to the true shortest-path distance from the root.
DepthCorrect ==
  Terminated => \A n \in Nodes : Len(PPath(n)) - 1 = Dist(n)

\* Eventually all queues become empty.
Termination == <>Terminated

THEOREM Spec => [](TypeOK /\ DepthCorrect)
THEOREM Spec => Termination
================================================================================