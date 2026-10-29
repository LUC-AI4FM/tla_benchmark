------------------------------- MODULE EchoTinyGraph -------------------------------
(***************************************************************************)
(* A tiny, fully connected, undirected graph with three nodes "a", "b",   *)
(* "c", for use with the Echo algorithm. The Echo algorithm is included   *)
(* inline so that the module is self-contained. It is meant for model     *)
(* checking and demonstration, not for generality.                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Several equivalent ways to define the set of nodes.                    *)
(***************************************************************************)
NodesExplicit == {"a", "b", "c"}

NodesByDomain == DOMAIN [a |-> 1, b |-> 2, c |-> 3]

Nodes == NodesExplicit

ASSUME NodesExplicit = NodesByDomain

initiator == "a"

NoNode == CHOOSE x : x \notin Nodes

(***************************************************************************)
(* Properties of an edge relation, represented as a Boolean function on   *)
(* pairs of nodes.                                                        *)
(***************************************************************************)
IsIrreflexive(r) == \A n \in Nodes : ~ r[n, n]

IsSymmetric(r) == \A m, n \in Nodes : r[m, n] = r[n, m]

\* With three nodes, every simple path between two nodes has length <= 2.
IsConnected(r) ==
    \A m, n \in Nodes :
        m # n => (r[m, n] \/ \E k \in Nodes : r[m, k] /\ r[k, n])

IsFullyConnected(r) == \A m, n \in Nodes : m # n => r[m, n]

(***************************************************************************)
(* Several ways to define the edge relation.                              *)
(***************************************************************************)
\* Explicit definition: every pair of distinct nodes is connected.
RExplicit == [p \in Nodes \X Nodes |-> p[1] # p[2]]

\* Definition by choosing a relation that satisfies the requirements.
RChoose ==
    CHOOSE r \in [Nodes \X Nodes -> BOOLEAN] :
        /\ IsConnected(r)
        /\ IsSymmetric(r)
        /\ IsIrreflexive(r)
        /\ IsFullyConnected(r)

R == RChoose

ASSUME /\ IsConnected(R)
       /\ IsSymmetric(R)
       /\ IsIrreflexive(R)
       /\ R = RExplicit

nbrs(n) == {m \in Nodes : R[m, n]}

(***************************************************************************)
(* The Echo algorithm.                                                    *)
(* msgs   : set of in-transit messages <<from, to>> (at most one per      *)
(*          directed edge during a run).                                  *)
(* parent : the parent of each node in the constructed spanning tree.     *)
(* rcvd   : number of messages received by each node.                     *)
(***************************************************************************)
VARIABLES msgs, parent, rcvd

vars == <<msgs, parent, rcvd>>

TypeOK ==
    /\ msgs \subseteq (Nodes \X Nodes)
    /\ parent \in [Nodes -> Nodes \cup {NoNode}]
    /\ rcvd \in [Nodes -> 0 .. Cardinality(Nodes)]

Init ==
    /\ msgs = {<<initiator, q>> : q \in nbrs(initiator)}
    /\ parent = [n \in Nodes |-> NoNode]
    /\ rcvd = [n \in Nodes |-> 0]

Receive(n) ==
    \E m \in msgs :
        /\ m[2] = n
        /\ LET sender   == m[1]
               first    == rcvd[n] = 0 /\ n # initiator
               newPar   == IF first THEN sender ELSE parent[n]
               newRcvd  == rcvd[n] + 1
               explore  == IF first
                             THEN {<<n, q>> : q \in nbrs(n) \ {sender}}
                             ELSE {}
               echo     == IF newRcvd = Cardinality(nbrs(n)) /\ n # initiator
                             THEN {<<n, newPar>>}
                             ELSE {}
           IN  /\ parent' = [parent EXCEPT ![n] = newPar]
               /\ rcvd' = [rcvd EXCEPT ![n] = newRcvd]
               /\ msgs' = (msgs \ {m}) \cup explore \cup echo

Terminated == rcvd[initiator] = Cardinality(nbrs(initiator))

Done == Terminated /\ msgs = {} /\ UNCHANGED vars

Next == (\E n \in Nodes : Receive(n)) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Nodes : Receive(n))

(***************************************************************************)
(* Properties.                                                            *)
(***************************************************************************)
\* When the initiator terminates, all other nodes have a parent that is a
\* neighbor, i.e., a spanning tree rooted at the initiator has been built.
SpanningTree ==
    Terminated =>
        /\ msgs = {}
        /\ \A n \in Nodes \ {initiator} : parent[n] \in nbrs(n)
        /\ parent[initiator] = NoNode

ParentIsNeighbor ==
    \A n \in Nodes : parent[n] # NoNode => parent[n] \in nbrs(n)

Liveness == <>Terminated

(***************************************************************************)
(* Test specification: prints the chosen relation, then runs Echo's Spec. *)
(***************************************************************************)
TestSpec == PrintT(R) /\ Spec

(***************************************************************************)
(* Postcondition for TLC.                                                 *)
(***************************************************************************)
PostCondition ==
    /\ R = RExplicit
    /\ IsConnected(R) /\ IsSymmetric(R) /\ IsIrreflexive(R)

THEOREM Spec => [](TypeOK /\ ParentIsNeighbor /\ SpanningTree)
THEOREM Spec => Liveness
=============================================================================