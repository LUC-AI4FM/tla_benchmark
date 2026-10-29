------------------------------- MODULE MCEcho -------------------------------
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Concrete instance data for model checking                              *)
(***************************************************************************)

\* A tiny graph consisting of three nodes
N1 == {1, 2, 3}

\* The initiator is chosen nondeterministically among the nodes
I1 == CHOOSE n \in N1 : TRUE

\* Graph as a function over node pairs (TRUE iff there is an edge)
G1 == [e \in N1 \X N1 |-> e \in {<<1,2>>, <<2,1>>, <<1,3>>, <<3,1>>}]

\* Auxiliary relational operators
Compose(r, s, S) ==
  {p \in S \X S : \E b \in S : <<p[1], b>> \in r /\ <<b, p[2]>> \in s}

RECURSIVE TCIter(_, _, _, _)
TCIter(s, r, S, k) ==
  IF k = 0 THEN s ELSE TCIter(s \cup Compose(s, r, S), r, S, k - 1)

TransitiveClosure(r, S) == TCIter(r, r, S, Cardinality(S))

IsIrreflexive(r, S) == \A n \in S : <<n, n>> \notin r
IsSymmetric(r, S)   == \A m, n \in S : <<m, n>> \in r => <<n, m>> \in r
IsConnected(r, S)   ==
  \A m, n \in S : m = n \/ <<m, n>> \in TransitiveClosure(r, S)

\* Graph chosen to satisfy connectivity, symmetry and irreflexivity
R1 == CHOOSE r \in SUBSET (N1 \X N1) :
         /\ IsConnected(r, N1)
         /\ IsSymmetric(r, N1)
         /\ IsIrreflexive(r, N1)

(***************************************************************************)
(* The echo protocol, instantiated with the concrete data above            *)
(***************************************************************************)

Node      == N1
initiator == I1
R         == R1

NoNode == CHOOSE x : x \notin Node

nbrs(n) == {m \in Node : <<n, m>> \in R}

ASSUME initiator \in Node
ASSUME IsConnected(R, Node) /\ IsSymmetric(R, Node) /\ IsIrreflexive(R, Node)

VARIABLES msgs,    \* set of messages <<sender, receiver>> in transit
          rcvd,    \* rcvd[n]: set of neighbors n has heard from
          parent,  \* parent[n]: parent of n in the spanning tree
          state    \* state[n] \in {"idle", "active", "done"}

vars == <<msgs, rcvd, parent, state>>

TypeOK ==
  /\ msgs \subseteq Node \X Node
  /\ rcvd \in [Node -> SUBSET Node]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ state \in [Node -> {"idle", "active", "done"}]

Init ==
  /\ msgs   = {<<initiator, m>> : m \in nbrs(initiator)}
  /\ rcvd   = [n \in Node |-> {}]
  /\ parent = [n \in Node |-> IF n = initiator THEN initiator ELSE NoNode]
  /\ state  = [n \in Node |-> IF n = initiator THEN "active" ELSE "idle"]

\* Node n receives a message from neighbor m
Receive(n, m) ==
  /\ <<m, n>> \in msgs
  /\ msgs' = (msgs \ {<<m, n>>})
               \cup (IF state[n] = "idle"
                       THEN {<<n, k>> : k \in nbrs(n) \ {m}}
                       ELSE {})
  /\ rcvd'   = [rcvd EXCEPT ![n] = @ \cup {m}]
  /\ parent' = IF state[n] = "idle"
                 THEN [parent EXCEPT ![n] = m]
                 ELSE parent
  /\ state'  = IF state[n] = "idle"
                 THEN [state EXCEPT ![n] = "active"]
                 ELSE state

\* Node n has heard from all neighbors: echo to parent and finish
Finish(n) ==
  /\ state[n] = "active"
  /\ rcvd[n] = nbrs(n)
  /\ msgs' = IF n = initiator THEN msgs ELSE msgs \cup {<<n, parent[n]>>}
  /\ state' = [state EXCEPT ![n] = "done"]
  /\ UNCHANGED <<rcvd, parent>>

Terminated ==
  /\ state[initiator] = "done"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Node : \E m \in nbrs(n) : Receive(n, m)
  \/ \E n \in Node : Finish(n)
  \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

ParentIsNeighbor ==
  \A n \in Node \ {initiator} : parent[n] # NoNode => parent[n] \in nbrs(n)

ParentRel == {<<n, parent[n]>> : n \in {k \in Node \ {initiator} : parent[k] # NoNode}}

\* When the initiator is done, all nodes are done and parents form a
\* spanning tree rooted at the initiator.
SpanningTree ==
  state[initiator] = "done" =>
    /\ \A n \in Node : state[n] = "done"
    /\ \A n \in Node \ {initiator} :
          /\ parent[n] \in nbrs(n)
          /\ <<n, initiator>> \in TransitiveClosure(ParentRel, Node)
    /\ msgs = {}

Termination == <>(state[initiator] = "done")

THEOREM Spec => [](TypeOK /\ ParentIsNeighbor /\ SpanningTree)

(***************************************************************************)
(* TLC-specific definitions                                                *)
(***************************************************************************)

\* Print the relation at startup, then run the protocol
TestSpec == PrintT(<<"R1", R1>>) /\ Spec

\* A simple view
MCView == <<msgs, rcvd, parent, state>>

\* Postcondition checked after model checking
PostCondition == TLCGet("stats").distinct > 0

=============================================================================