------------------------------- MODULE YoYoLeaderElection -------------------------------
(***************************************************************************)
(* The Yo-Yo leader election algorithm with pruning, on an arbitrary      *)
(* connected undirected graph. Each node has a unique natural-number id.  *)
(* The node with the minimum id is elected.                               *)
(*                                                                         *)
(* Edges are oriented from the smaller to the larger id. Each round has   *)
(* two phases:                                                             *)
(*  - "down" (Yo-): sources send their ids along outgoing edges. Internal *)
(*    nodes and sinks wait for values from all in-neighbours, then forward*)
(*    the minimum of those values.                                         *)
(*  - "up" (-Yo): sinks reply YES to the in-neighbours that sent the      *)
(*    minimum and NO to the others. Internal nodes wait for replies from  *)
(*    all out-neighbours. If any reply is NO, they reply NO to all        *)
(*    in-neighbours. Otherwise they reply YES to in-neighbours that sent  *)
(*    the minimum and NO to the others.                                   *)
(* Every edge that carries a NO is reversed.                               *)
(*                                                                         *)
(* Pruning has two rules:                                                  *)
(*  - A sink with exactly one in-neighbour removes itself.                *)
(*  - If several in-neighbours sent the same value, only one edge is kept *)
(*    and the others are pruned.                                          *)
(*                                                                         *)
(* A node that remains active with no edges is the leader.                *)
(*                                                                         *)
(* Example configurations (in a .cfg file):                               *)
(*   Nodes = {1,2,3,4}  Edges = {{1,2},{2,3},{3,4},{4,1}}        ring     *)
(*   Nodes = {2,5,7,9}  Edges = {{2,5},{5,7},{7,9},{2,9},{5,9}}           *)
(*   Nodes = {3,1,4,6,8} Edges = {{3,1},{3,4},{3,6},{3,8}}       star     *)
(*   Nodes = {1,2,3}    Edges = {{1,2},{2,3},{1,3}}              triangle *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges

ASSUME NodesAreIds == Nodes \subseteq Nat /\ Nodes # {} /\ IsFiniteSet(Nodes)

ASSUME EdgesWellFormed ==
  Edges \subseteq {{m, n} : m \in Nodes, n \in Nodes \ {m}}

\* Connectivity: every proper nonempty subset of nodes has an edge leaving it.
ASSUME GraphConnected ==
  \A S \in SUBSET Nodes :
     (S # {} /\ S # Nodes) => \E e \in Edges : e \cap S # {} /\ e \ S # {}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

MinNode == Min(Nodes)

VARIABLES
  active,    \* active[n]: n has not been pruned
  phase,     \* phase[n] \in {"down","up"}
  incoming,  \* incoming[n]: in-neighbours of n (edges oriented towards n)
  outgoing,  \* outgoing[n]: out-neighbours of n (edges oriented away from n)
  mailbox,   \* mailbox[n]: set of messages delivered to n, not yet consumed
  rcvd,      \* rcvd[n]: function: in-neighbour -> value received in down phase
  myval      \* myval[n]: value n forwarded in the current down phase

vars == <<active, phase, incoming, outgoing, mailbox, rcvd, myval>>

(* All messages use one record shape so that TLC can compare them. *)
DownMsg(s, v) ==
  [type |-> "down", sndr |-> s, val |-> v, reply |-> "none", prune |-> FALSE]
UpMsg(s, r, p) ==
  [type |-> "up", sndr |-> s, val |-> 0, reply |-> r, prune |-> p]

Messages ==
  [type : {"down"}, sndr : Nodes, val : Nodes, reply : {"none"}, prune : {FALSE}]
  \cup
  [type : {"up"}, sndr : Nodes, val : {0}, reply : {"yes", "no"}, prune : BOOLEAN]

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]
  /\ \A n \in Nodes : DOMAIN rcvd[n] \subseteq Nodes
  /\ myval \in [Nodes -> Nodes]

Init ==
  /\ active = [n \in Nodes |-> TRUE]
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]
  /\ rcvd = [n \in Nodes |-> [m \in {} |-> 0]]
  /\ myval = [n \in Nodes |-> n]

(***************************************************************************)
(* Down phase (Yo-).                                                       *)
(* A source sends its own id. Any other node first waits for one value    *)
(* from each in-neighbour, then forwards their minimum.                   *)
(***************************************************************************)
Down(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] \cup outgoing[n] # {}
  /\ LET dm == {msg \in mailbox[n] : msg.type = "down" /\ msg.sndr \in incoming[n]}
         v  == IF incoming[n] = {} THEN n ELSE Min({msg.val : msg \in dm})
     IN  /\ {msg.sndr : msg \in dm} = incoming[n]
         /\ rcvd' = [rcvd EXCEPT ![n] =
                       [m \in incoming[n] |-> (CHOOSE msg \in dm : msg.sndr = m).val]]
         /\ myval' = [myval EXCEPT ![n] = v]
         /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ dm
                          ELSE IF m \in outgoing[n]
                               THEN mailbox[m] \cup {DownMsg(n, v)}
                               ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(***************************************************************************)
(* Up phase (-Yo), with edge reversal and pruning.                        *)
(* A node waits for replies from all out-neighbours (a sink waits for     *)
(* none), sends replies to its in-neighbours, then updates the            *)
(* orientation of its edges.                                              *)
(***************************************************************************)
Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ LET um        == {msg \in mailbox[n] : msg.type = "up" /\ msg.sndr \in outgoing[n]}
         inN       == incoming[n]
         vals      == rcvd[n]
         allYes    == \A msg \in um : msg.reply = "yes"
         prunedOut == {msg.sndr : msg \in {x \in um : x.prune}}
         flipOut   == {msg.sndr : msg \in {x \in um : x.reply = "no" /\ ~x.prune}}
         selfPrune == outgoing[n] = {} /\ Cardinality(inN) = 1
         pruneIn   == IF selfPrune THEN inN
                      ELSE {m \in inN :
                              m # Min({k \in inN : vals[k] = vals[m]})}
         yes(m)    == allYes /\ vals[m] = myval[n]
         noIn      == {m \in inN : ~yes(m)}
         flipIn    == noIn \ pruneIn
     IN  /\ {msg.sndr : msg \in um} = outgoing[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ um
                          ELSE IF m \in inN
                               THEN mailbox[m] \cup
                                      {UpMsg(n, IF yes(m) THEN "yes" ELSE "no",
                                             m \in pruneIn)}
                               ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] =
                           IF selfPrune THEN {}
                           ELSE (inN \ (pruneIn \cup noIn)) \cup flipOut]
         /\ outgoing' = [outgoing EXCEPT ![n] =
                           IF selfPrune THEN {}
                           ELSE (outgoing[n] \ (prunedOut \cup flipOut)) \cup flipIn]
         /\ active' = [active EXCEPT ![n] = ~selfPrune]
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ UNCHANGED <<rcvd, myval>>

(***************************************************************************)
(* Leader and termination.                                                 *)
(***************************************************************************)
IsLeader(n) == active[n] /\ incoming[n] = {} /\ outgoing[n] = {}

Leaders == {n \in Nodes : IsLeader(n)}

Terminated == Leaders # {}

\* Stuttering after termination, so that the final state is not a deadlock.
Done == Terminated /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes : Down(n) \/ Up(n)
  \/ Done

Fairness == \A n \in Nodes : WF_vars(Down(n)) /\ WF_vars(Up(n))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
\* At most one node is ever elected.
AtMostOneLeader == Cardinality(Leaders) <= 1

\* Any elected leader is the node with the minimum identifier.
LeaderIsMin == \A n \in Leaders : n = MinNode

\* The minimum node is never pruned.
MinNeverPruned == active[MinNode]

\* Agreement: once a leader exists, every other node knows it is not the
\* leader, because it has been eliminated.
Agreement ==
  Terminated =>
     \A n \in Nodes : (n = MinNode /\ IsLeader(n)) \/ (n # MinNode /\ ~active[n])

SafetyInv == TypeOK /\ AtMostOneLeader /\ LeaderIsMin /\ MinNeverPruned /\ Agreement

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* Eventually exactly one leader, the minimum node, is elected.
EventualElection == <>(Leaders = {MinNode})

\* Once elected, the leader remains the unique leader forever.
StableElection == <>[](Leaders = {MinNode})

\* Eventually all nodes agree on the outcome, permanently.
EventualAgreement ==
  <>[](\A n \in Nodes : IF n = MinNode THEN IsLeader(n) ELSE ~active[n])

THEOREM Spec => [](TypeOK /\ AtMostOneLeader /\ LeaderIsMin /\ Agreement)
THEOREM Spec => EventualElection /\ StableElection /\ EventualAgreement
==========================================================================================