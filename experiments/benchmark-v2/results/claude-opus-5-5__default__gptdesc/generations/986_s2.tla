---------------------------- MODULE YoYoPruning ----------------------------
(***************************************************************************)
(* Yo-Yo leader election on a connected undirected graph, extended with   *)
(* pruning so that the algorithm terminates.  Edges are initially          *)
(* oriented from the smaller to the larger node identity.  In each round,  *)
(* nodes perform a "down" (Yo-) phase and an "up" (-Yo) phase:             *)
(*  - Down: a source sends its own identity to all out-neighbors; any     *)
(*    other node waits for values from all in-neighbors and forwards the  *)
(*    minimum to all out-neighbors.                                        *)
(*  - Up: a node waits for replies from all out-neighbors, then replies   *)
(*    to its in-neighbors.  It replies "yes" to the senders of the minimum *)
(*    value if all its out-neighbors replied "yes", and "no" otherwise.    *)
(*    Edges over which "no" is sent are reversed.                          *)
(*  - Pruning: if several in-neighbors sent the same value, all but one of *)
(*    them are asked to prune their edge.  A sink that received only a     *)
(*    single distinct value is a leaf: it prunes all its edges and becomes *)
(*    inactive.                                                            *)
(* Eventually only the smallest node remains active and it is isolated:   *)
(* it is the leader.                                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

ReachableFrom(n) ==
  LET R[k \in 0 .. Cardinality(Nodes)] ==
        IF k = 0 THEN {n}
        ELSE R[k-1] \cup UNION {Neighbors(x) : x \in R[k-1]}
  IN  R[Cardinality(Nodes)]

ASSUME
  /\ IsFiniteSet(Nodes)
  /\ Nodes # {}
  /\ Nodes \subseteq Nat
  /\ Edges \subseteq {{m, n} : m, n \in Nodes}
  /\ \A e \in Edges : Cardinality(e) = 2
  /\ \A m, n \in Nodes : n \in ReachableFrom(m)

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Leader == Min(Nodes)

DownMsg == [phase : {"down"}, sndr : Nodes, val : Nodes]
UpMsg   == [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]
Messages == DownMsg \cup UpMsg

VARIABLES
  active,    \* active[n]: node n has not been pruned
  phase,     \* phase[n] \in {"down", "up"}
  incoming,  \* incoming[n]: n's view of its in-neighbors
  outgoing,  \* outgoing[n]: n's view of its out-neighbors
  mailbox    \* mailbox[n]: set of messages received by n

vars == <<active, phase, incoming, outgoing, mailbox>>

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

Init ==
  /\ active = [n \in Nodes |-> TRUE]
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : n < m}]
  /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase.                                                             *)
(***************************************************************************)
DownAction(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] \cup outgoing[n] # {}
  /\ LET recv == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
     IN  /\ {msg.sndr : msg \in recv} = incoming[n]
         /\ LET v == IF incoming[n] = {} THEN n
                     ELSE Min({msg.val : msg \in recv})
            IN  mailbox' = [k \in Nodes |->
                              IF k \in outgoing[n]
                              THEN mailbox[k] \cup {[phase |-> "down", sndr |-> n, val |-> v]}
                              ELSE mailbox[k]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(***************************************************************************)
(* Up phase, including edge reversal and pruning.                          *)
(***************************************************************************)
UpAction(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ LET ups  == {msg \in mailbox[n] : msg.phase = "up"}
         recv == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
         vals == {msg.val : msg \in recv}
         allYes == \A msg \in ups : msg.reply = "yes"
         ValOf(m) == (CHOOSE msg \in recv : msg.sndr = m).val
         keep == {Min({x.sndr : x \in {y \in recv : y.val = w}}) : w \in vals}
         leaf == outgoing[n] = {} /\ Cardinality(vals) = 1
         Pruned(m) == leaf \/ m \notin keep
         Reply(m) == IF allYes /\ ValOf(m) = Min(vals) THEN "yes" ELSE "no"
         outYes == {x.sndr : x \in {y \in ups : y.reply = "yes" /\ ~y.prune}}
         outNo  == {x.sndr : x \in {y \in ups : y.reply = "no" /\ ~y.prune}}
         inYes  == {m \in incoming[n] : ~Pruned(m) /\ Reply(m) = "yes"}
         inNo   == {m \in incoming[n] : ~Pruned(m) /\ Reply(m) = "no"}
     IN  /\ {msg.sndr : msg \in ups} = outgoing[n]
         /\ {msg.sndr : msg \in recv} = incoming[n]
         /\ mailbox' = [k \in Nodes |->
                          IF k = n THEN mailbox[n] \ (ups \cup recv)
                          ELSE IF k \in incoming[n]
                               THEN mailbox[k] \cup
                                      {[phase |-> "up", sndr |-> n,
                                        reply |-> Reply(k), prune |-> Pruned(k)]}
                               ELSE mailbox[k]]
         /\ incoming' = [incoming EXCEPT ![n] = IF leaf THEN {} ELSE inYes \cup outNo]
         /\ outgoing' = [outgoing EXCEPT ![n] = IF leaf THEN {} ELSE outYes \cup inNo]
         /\ active' = [active EXCEPT ![n] = ~leaf]
         /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : DownAction(n) \/ UpAction(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)
EdgesAreNeighbors ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] \subseteq Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}
     /\ n \notin incoming[n] \cup outgoing[n]

InactiveNodesIsolated ==
  \A n \in Nodes : ~active[n] => incoming[n] = {} /\ outgoing[n] = {}

NoPending(n, m) ==
  /\ \A msg \in mailbox[n] : msg.sndr # m
  /\ \A msg \in mailbox[m] : msg.sndr # n

\* At round boundaries the local views of the two endpoints of an edge agree.
GraphConsistent ==
  \A n, m \in Nodes :
     (phase[n] = "down" /\ phase[m] = "down" /\ NoPending(n, m))
       => (m \in outgoing[n] <=> n \in incoming[m])

LeaderStaysSource ==
  active[Leader] /\ incoming[Leader] = {}

Terminated ==
  /\ \A n \in Nodes :
        IF n = Leader
        THEN active[n] /\ incoming[n] = {} /\ outgoing[n] = {}
        ELSE ~active[n]
  /\ \A n \in Nodes : mailbox[n] = {}

(***************************************************************************)
(* Liveness / termination properties.                                      *)
(***************************************************************************)
EventuallyTerminates == <>Terminated

TerminationIsStable == [](Terminated => []Terminated)

DeadlockIffTerminated == [](~(ENABLED Next) <=> Terminated)

=============================================================================