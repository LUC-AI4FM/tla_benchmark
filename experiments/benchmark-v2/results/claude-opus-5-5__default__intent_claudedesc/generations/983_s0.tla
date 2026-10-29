---------------------------- MODULE YoYoPruning ----------------------------
(***************************************************************************)
(* Yo-Yo leader election with pruning on an arbitrary connected,          *)
(* undirected graph.  Edges are initially oriented from the smaller to    *)
(* the larger identifier.                                                  *)
(*   - source   : node with no in-neighbours (a candidate)                 *)
(*   - internal : node with both in- and out-neighbours                    *)
(*   - sink     : node with no out-neighbours                              *)
(*                                                                         *)
(* Down (Yo-) phase: sources send their identifier to their               *)
(* out-neighbours.  Internal nodes wait for values from all in-neighbours  *)
(* and forward the minimum.  Sinks collect the values from all            *)
(* in-neighbours.                                                          *)
(*                                                                         *)
(* Up (-Yo) phase: each node replies YES to the in-neighbours that sent   *)
(* the minimum value and NO to the others.  An internal node that receives *)
(* a NO from any out-neighbour replies NO to all of its in-neighbours.    *)
(* Every edge that carries a NO is reversed.                               *)
(*                                                                         *)
(* Pruning:                                                                *)
(*   - When several in-neighbours sent the same value, all but one are    *)
(*     asked to prune their edge.                                          *)
(*   - A sink that received a single value (a leaf after duplicate        *)
(*     pruning) prunes itself and becomes inactive.                        *)
(*                                                                         *)
(* Messages carry round numbers, because neighbours may be in different   *)
(* rounds at the same time.                                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,   \* set of node identifiers (natural numbers)
          Edges    \* set of undirected edges, each a 2-element set of nodes

ASSUME NodesAssump == Nodes # {} /\ IsFiniteSet(Nodes) /\ Nodes \subseteq Nat

ASSUME EdgesAssump ==
  /\ Edges \subseteq SUBSET Nodes
  /\ \A e \in Edges : Cardinality(e) = 2

\* The graph is connected: every proper non-empty cut is crossed by an edge.
ASSUME ConnectedAssump ==
  \A S \in SUBSET Nodes :
     (S # {} /\ S # Nodes) => \E e \in Edges : e \cap S # {} /\ e \ S # {}

VARIABLES
  active,   \* active[n] : node n has not been pruned
  nbrs,     \* nbrs[n]   : n's current (non-pruned) neighbours
  out,      \* out[n]    : n's current out-neighbours (subset of nbrs[n])
  phase,    \* phase[n]  : "down" or "up"
  round,    \* round[n]  : current round of node n
  mailbox   \* mailbox[n]: set of messages received by n

vars == <<active, nbrs, out, phase, round, mailbox>>

-----------------------------------------------------------------------------
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

InitNbrs(n) == {m \in Nodes : {n, m} \in Edges}

Msgs == [type : {"down", "up"}, sndr : Nodes, val : Nodes,
         reply : {"yes", "no", "none"}, prune : BOOLEAN, rnd : Nat]

DownMsg(s, v, r) == [type |-> "down", sndr |-> s, val |-> v,
                     reply |-> "none", prune |-> FALSE, rnd |-> r]

UpMsg(s, rep, p, r) == [type |-> "up", sndr |-> s, val |-> s,
                        reply |-> rep, prune |-> p, rnd |-> r]

In(n)  == nbrs[n] \ out[n]
Out(n) == out[n]

DownRcvd(n) == {msg \in mailbox[n] : msg.type = "down" /\ msg.rnd = round[n]}
UpRcvd(n)   == {msg \in mailbox[n] : msg.type = "up"   /\ msg.rnd = round[n]}

AllDown(n) == \A m \in In(n)  : \E msg \in DownRcvd(n) : msg.sndr = m
AllUp(n)   == \A m \in Out(n) : \E msg \in UpRcvd(n)   : msg.sndr = m

ValOf(n, m) == (CHOOSE msg \in DownRcvd(n) : msg.sndr = m).val
MinVal(n)   == Min({ValOf(n, m) : m \in In(n)})

\* Among the in-neighbours that sent value v, keep only the smallest one.
Keeper(n, v) == Min({m \in In(n) : ValOf(n, m) = v})
PruneSet(n)  == {m \in In(n) : m # Keeper(n, ValOf(n, m))}

\* Messages remaining after n finishes its current round.
Clean(n) == {msg \in mailbox[n] : msg.rnd # round[n]}

-----------------------------------------------------------------------------
Init ==
  /\ active  = [n \in Nodes |-> TRUE]
  /\ nbrs    = [n \in Nodes |-> InitNbrs(n)]
  /\ out     = [n \in Nodes |-> {m \in InitNbrs(n) : n < m}]
  /\ phase   = [n \in Nodes |-> "down"]
  /\ round   = [n \in Nodes |-> 0]
  /\ mailbox = [n \in Nodes |-> {}]

(* Down phase at a source: send own identifier to all out-neighbours. *)
DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ In(n) = {}
  /\ Out(n) # {}
  /\ mailbox' = [m \in Nodes |->
                   IF m \in Out(n)
                   THEN mailbox[m] \cup {DownMsg(n, n, round[n])}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, nbrs, out, round>>

(* Down phase at an internal node: forward the minimum received value. *)
DownInternal(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ In(n) # {}
  /\ Out(n) # {}
  /\ AllDown(n)
  /\ mailbox' = [m \in Nodes |->
                   IF m \in Out(n)
                   THEN mailbox[m] \cup {DownMsg(n, MinVal(n), round[n])}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, nbrs, out, round>>

(* A sink receives all values, replies immediately (starting the up      *)
(* phase), and possibly prunes itself.  This ends its round.             *)
SinkStep(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ In(n) # {}
  /\ Out(n) = {}
  /\ AllDown(n)
  /\ LET vals     == {ValOf(n, m) : m \in In(n)}
         leaf     == Cardinality(vals) = 1
         Reply(m) == IF ValOf(n, m) = MinVal(n) THEN "yes" ELSE "no"
         Pr(m)    == leaf \/ m \in PruneSet(n)
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m \in In(n)
                          THEN mailbox[m] \cup {UpMsg(n, Reply(m), Pr(m), round[n])}
                          ELSE IF m = n
                               THEN (IF leaf THEN {} ELSE Clean(n))
                               ELSE mailbox[m]]
         /\ active' = [active EXCEPT ![n] = ~leaf]
         /\ nbrs'   = [nbrs EXCEPT ![n] = IF leaf THEN {} ELSE @ \ PruneSet(n)]
         /\ out'    = [out EXCEPT ![n] =
                         IF leaf THEN {}
                         ELSE {m \in In(n) \ PruneSet(n) : Reply(m) = "no"}]
         /\ round'  = [round EXCEPT ![n] = @ + 1]
         /\ UNCHANGED phase

(* Up phase at a source or an internal node: collect the replies from all *)
(* out-neighbours, reverse or prune edges, and (for internal nodes) reply *)
(* to the in-neighbours.  This ends the node's round.                     *)
UpStep(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ AllUp(n)
  /\ LET UpOf(m)   == CHOOSE msg \in UpRcvd(n) : msg.sndr = m
         prunedOut == {m \in Out(n) : UpOf(m).prune}
         flipped   == {m \in Out(n) : UpOf(m).reply = "no" /\ ~UpOf(m).prune}
         allYes    == \A m \in Out(n) : UpOf(m).reply = "yes"
         Reply(m)  == IF allYes /\ ValOf(n, m) = MinVal(n) THEN "yes" ELSE "no"
         newOut    == (Out(n) \ (prunedOut \cup flipped))
                        \cup {m \in In(n) \ PruneSet(n) : Reply(m) = "no"}
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m \in In(n)
                          THEN mailbox[m] \cup
                                 {UpMsg(n, Reply(m), m \in PruneSet(n), round[n])}
                          ELSE IF m = n THEN Clean(n) ELSE mailbox[m]]
         /\ nbrs'  = [nbrs EXCEPT ![n] = @ \ (prunedOut \cup PruneSet(n))]
         /\ out'   = [out EXCEPT ![n] = newOut]
         /\ phase' = [phase EXCEPT ![n] = "down"]
         /\ round' = [round EXCEPT ![n] = @ + 1]
         /\ UNCHANGED active

Step(n) == DownSource(n) \/ DownInternal(n) \/ SinkStep(n) \/ UpStep(n)

ActiveNodes == {n \in Nodes : active[n]}

Terminated == ActiveNodes = {MinNode} /\ nbrs[MinNode] = {}

Next == (\E n \in Nodes : Step(n))
        \/ (Terminated /\ UNCHANGED vars)

Fairness == \A n \in Nodes : WF_vars(Step(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
  /\ active  \in [Nodes -> BOOLEAN]
  /\ nbrs    \in [Nodes -> SUBSET Nodes]
  /\ out     \in [Nodes -> SUBSET Nodes]
  /\ \A n \in Nodes : out[n] \subseteq nbrs[n] /\ n \notin nbrs[n]
  /\ phase   \in [Nodes -> {"down", "up"}]
  /\ round   \in [Nodes -> Nat]
  /\ mailbox \in [Nodes -> SUBSET Msgs]

\* Consistency: the minimum node is never eliminated from candidacy.
MinNeverPruned == active[MinNode]

\* The minimum node always remains a source (an active candidate).
MinRemainsSource == In(MinNode) = {}

\* Some node is always active.
SomeNodeActive == ActiveNodes # {}

\* Pruned nodes have left the graph.
PrunedDetached == \A n \in Nodes : ~active[n] => nbrs[n] = {}

\* Only the minimum node can end up isolated while still active.
OnlyMinIsolated == \A n \in Nodes : (active[n] /\ nbrs[n] = {}) => n = MinNode

\* Leader election (safety part): on termination, the unique active node is
\* the node with the minimum identifier.
LeaderSafety == Terminated => ActiveNodes = {MinNode}

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Termination: the algorithm eventually terminates and stays terminated.
Termination == <>[]Terminated

\* Leader election: eventually exactly one node (the minimum) remains active.
LeaderElection == <>[](ActiveNodes = {MinNode})

\* Progress: while more than one node is active, some non-minimum node is
\* eventually pruned.
Progress ==
  \A k \in 2..Cardinality(Nodes) :
     (Cardinality(ActiveNodes) = k) ~> (Cardinality(ActiveNodes) < k)

\* The number of active nodes never increases.
ActiveMonotone == [][ActiveNodes' \subseteq ActiveNodes]_vars

THEOREM Spec => [](TypeOK /\ MinNeverPruned /\ MinRemainsSource /\ SomeNodeActive
                   /\ PrunedDetached /\ OnlyMinIsolated /\ LeaderSafety)
THEOREM Spec => Termination /\ LeaderElection /\ Progress /\ ActiveMonotone
=============================================================================