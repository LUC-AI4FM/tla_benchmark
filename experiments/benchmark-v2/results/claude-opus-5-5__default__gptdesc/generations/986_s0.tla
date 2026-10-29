---------------------------- MODULE YoYoPruning ----------------------------
(***************************************************************************)
(* The Yo-Yo leader election algorithm on a connected undirected graph,  *)
(* extended with pruning so that the algorithm terminates.                *)
(*                                                                         *)
(* Edges are initially oriented from the smaller to the larger node.      *)
(* Nodes alternate between a down phase and an up phase:                   *)
(*  - Down phase: a source sends its own id to all out-neighbors. Other   *)
(*    nodes wait for values from all in-neighbors and forward the         *)
(*    minimum to their out-neighbors.                                      *)
(*  - Up phase: a node waits for replies from all out-neighbors. It       *)
(*    replies "yes" to the in-neighbors that sent the minimum value,      *)
(*    unless it received a "no" from below. Every edge on which "no" is   *)
(*    sent is reversed.                                                    *)
(*  - Pruning: if several in-neighbors sent the same value, all but one   *)
(*    of those edges are pruned. A sink that received only one distinct   *)
(*    value prunes all of its incoming edges and becomes isolated.         *)
(* Eventually every edge is pruned, and the smallest node, which is a     *)
(* source throughout, is the last node left as the leader.                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges

RECURSIVE Reach(_)
Reach(S) ==
  LET T == S \cup {m \in Nodes : \E n \in S : {m, n} \in Edges}
  IN  IF T = S THEN S ELSE Reach(T)

IsUndirectedGraph ==
  \A e \in Edges : \E m, n \in Nodes : m # n /\ e = {m, n}

IsConnected == \A n \in Nodes : Reach({n}) = Nodes

ASSUME
  /\ IsFiniteSet(Nodes)
  /\ Nodes # {}
  /\ Nodes \subseteq Nat
  /\ IsUndirectedGraph
  /\ IsConnected

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

Messages ==
       [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]

VARIABLES
  phase,     \* phase[n] \in {"down", "up"}
  incoming,  \* incoming[n]: current in-neighbors of n
  outgoing,  \* outgoing[n]: current out-neighbors of n
  mailbox    \* mailbox[n]: set of messages pending at n

vars == <<phase, incoming, outgoing, mailbox>>

DownMsgs(n) == {msg \in mailbox[n] : msg.phase = "down"}
UpMsgs(n)   == {msg \in mailbox[n] : msg.phase = "up"}

kind(n) ==
  IF incoming[n] = {} /\ outgoing[n] = {} THEN "isolated"
  ELSE IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

-----------------------------------------------------------------------------
Init ==
  /\ phase    = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : n < m}]
  /\ mailbox  = [n \in Nodes |-> {}]

(* Down phase: sources send their own id. Other nodes wait for values from *)
(* all in-neighbors and forward the minimum.                               *)
Down(n) ==
  /\ phase[n] = "down"
  /\ kind(n) # "isolated"
  /\ \A m \in incoming[n] : \E msg \in DownMsgs(n) : msg.sndr = m
  /\ LET v   == IF incoming[n] = {} THEN n
                ELSE Min({msg.val : msg \in DownMsgs(n)})
         out == [phase |-> "down", sndr |-> n, val |-> v]
     IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n] THEN mailbox[m] \cup {out}
                       ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(* Up phase: collect replies from out-neighbors, answer in-neighbors,     *)
(* reverse edges on which "no" is sent or received, and prune edges.      *)
Up(n) ==
  /\ phase[n] = "up"
  /\ \A m \in incoming[n] : \E msg \in DownMsgs(n) : msg.sndr = m
  /\ \A k \in outgoing[n] : \E msg \in UpMsgs(n) : msg.sndr = k
  /\ LET dmsgs     == DownMsgs(n)
         umsgs     == UpMsgs(n)
         SVal(m)   == (CHOOSE msg \in dmsgs : msg.sndr = m).val
         Rep(k)    == CHOOSE msg \in umsgs : msg.sndr = k
         vals      == {SVal(m) : m \in incoming[n]}
         minVal    == IF vals = {} THEN n ELSE Min(vals)
         noBelow   == \E k \in outgoing[n] : Rep(k).reply = "no"
         keep      == {(CHOOSE m \in incoming[n] : SVal(m) = v) : v \in vals}
         pruned    == IF outgoing[n] = {} /\ Cardinality(vals) = 1
                      THEN incoming[n]
                      ELSE incoming[n] \ keep
         Answer(m) == IF ~noBelow /\ SVal(m) = minVal THEN "yes" ELSE "no"
         reversedIn  == {m \in incoming[n] \ pruned : Answer(m) = "no"}
         prunedOut   == {k \in outgoing[n] : Rep(k).prune}
         reversedOut == {k \in outgoing[n] \ prunedOut : Rep(k).reply = "no"}
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN {}
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup
                                      {[phase |-> "up", sndr |-> n,
                                        reply |-> Answer(m),
                                        prune |-> m \in pruned]}
                               ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] =
                           (incoming[n] \ (pruned \cup reversedIn)) \cup reversedOut]
         /\ outgoing' = [outgoing EXCEPT ![n] =
                           (outgoing[n] \ (prunedOut \cup reversedOut)) \cup reversedIn]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
  /\ phase    \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox  \in [Nodes -> SUBSET Messages]

\* Each node is linked only to graph neighbors, and no edge is both incoming and outgoing.
NeighborConsistency ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] \subseteq Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

\* Two nodes in the down phase agree on the direction of the edge between them.
EdgeConsistency ==
  \A m, n \in Nodes :
     (phase[m] = "down" /\ phase[n] = "down") =>
        (m \in outgoing[n] <=> n \in incoming[m])

\* The smallest node is never the target of an edge, so it stays a source.
MinIsSource == incoming[Min(Nodes)] = {}

\* Messages travel only along edges in the right direction.
MessageConsistency ==
  \A n \in Nodes : \A msg \in mailbox[n] :
     /\ msg.phase = "down" => msg.sndr \in incoming[n]
     /\ msg.phase = "up"   => msg.sndr \in outgoing[n]

-----------------------------------------------------------------------------
(* Termination properties *)

Terminated ==
  \A n \in Nodes :
     /\ incoming[n] = {}
     /\ outgoing[n] = {}
     /\ mailbox[n]  = {}

Leader == Min(Nodes)

\* At termination, the leader is the smallest node: the source that was never pruned.
LeaderCorrect == Terminated => kind(Leader) = "isolated"

EventuallyTerminates == <>Terminated

TerminationStable == [](Terminated => []Terminated)

DeadlockIffTerminated == [](~(ENABLED Next) <=> Terminated)

=============================================================================