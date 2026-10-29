---------------------------- MODULE YoYoLeaderElection ----------------------------
(***************************************************************************)
(* Yo-Yo leader election with pruning on an undirected, simple, connected *)
(* graph. Nodes are asynchronous and communicate by messages placed into  *)
(* the recipient's mailbox (a set of messages). Each round has a "down"   *)
(* phase, in which minimal identifiers flow along oriented edges, and an  *)
(* "up" phase, in which yes/no replies flow back.                         *)
(*                                                                         *)
(*  - A "no" reply reverses the orientation of the edge.                  *)
(*  - A reply carrying the prune flag removes the edge.                   *)
(*                                                                         *)
(* The algorithm terminates when exactly one node, the one with the       *)
(* minimum identifier, remains active and has no edges left. All other    *)
(* nodes are then inactive and all mailboxes are empty.                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,  \* node identifiers (distinct natural numbers)
          Edges   \* undirected edges, each a 2-element set of nodes

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE ReachFrom(_, _)
ReachFrom(S, k) ==
  IF k = 0 THEN S
  ELSE ReachFrom(S \cup UNION {Neighbors(x) : x \in S}, k - 1)

IsConnected == \A n \in Nodes : ReachFrom({n}, Cardinality(Nodes)) = Nodes

ASSUME /\ Nodes # {}
       /\ IsFiniteSet(Nodes)
       /\ Nodes \subseteq Nat
       /\ Edges \subseteq SUBSET Nodes
       /\ \A e \in Edges : Cardinality(e) = 2   \* simple graph, no self-loops
       /\ IsConnected

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

VARIABLES active,    \* active[n]: node n still participates
          phase,     \* phase[n] \in {"down", "up"}
          incoming,  \* incoming[n]: neighbors whose edge n views as incoming
          outgoing,  \* outgoing[n]: neighbors whose edge n views as outgoing
          mailbox    \* mailbox[n]: set of messages pending for n

vars == <<active, phase, incoming, outgoing, mailbox>>

Messages ==
  [phase : {"down", "up"}, sndr : Nodes, val : Nodes,
   reply : {"none", "yes", "no"}, prune : BOOLEAN]

DownMsg(s, v) ==
  [phase |-> "down", sndr |-> s, val |-> v, reply |-> "none", prune |-> FALSE]

UpMsg(s, r, p) ==
  [phase |-> "up", sndr |-> s, val |-> s, reply |-> r, prune |-> p]

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

-----------------------------------------------------------------------------
(* Initially every incident link is active and is oriented from the       *)
(* smaller identifier to the larger one.                                   *)
Init ==
  /\ active = [n \in Nodes |-> TRUE]
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

-----------------------------------------------------------------------------
(* "Down" messages of the current round, from the current in-neighbors.   *)
(* A message from a node that is not a current in-neighbor belongs to     *)
(* the next round, after a pending edge reversal, so it is not taken here. *)
CurrentDowns(n) ==
  {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}

(* Up replies from the current out-neighbors. *)
CurrentUps(n) ==
  {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

(* Down phase.                                                             *)
(*  - A source sends its own identifier along all outgoing edges.          *)
(*  - Any other node first waits for values from all in-neighbors. It then *)
(*    forwards their minimum along its outgoing edges; for a sink, that    *)
(*    set is empty.                                                        *)
Down(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ IF incoming[n] = {}
       THEN /\ outgoing[n] # {}   \* a source with no edges is the leader
            /\ mailbox' = [m \in Nodes |->
                             IF m \in outgoing[n]
                               THEN mailbox[m] \cup {DownMsg(n, n)}
                               ELSE mailbox[m]]
       ELSE LET downs == CurrentDowns(n)
                mn    == Min({d.val : d \in downs})
            IN  /\ {d.sndr : d \in downs} = incoming[n]
                /\ mailbox' = [m \in Nodes |->
                                 IF m \in outgoing[n]
                                   THEN mailbox[m] \cup {DownMsg(n, mn)}
                                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* Up phase. Node n waits for replies from all out-neighbors and then     *)
(* processes them:                                                         *)
(*  - "no" reverses the edge;                                              *)
(*  - a prune flag removes the edge.                                       *)
(* A non-source node then replies to its in-neighbors:                     *)
(*  - If all replies were "yes", or n is a sink, it answers "yes" to the   *)
(*    senders of the minimum and "no" to the others.                       *)
(*  - Otherwise it answers "no" to everyone.                               *)
(* Among several senders of the minimum, all but one nondeterministically  *)
(* chosen sender are pruned. If n would be left as a leaf sink, the        *)
(* remaining edge is pruned too and n becomes inactive.                    *)
Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ LET ups      == CurrentUps(n)
         noS      == {u.sndr : u \in {x \in ups : x.reply = "no"}}
         prS      == {u.sndr : u \in {x \in ups : x.prune}}
         outAfter == outgoing[n] \ (noS \cup prS)
         downs    == CurrentDowns(n)
         mn       == Min({d.val : d \in downs})
         minS     == {d.sndr : d \in {x \in downs : x.val = mn}}
         allYes   == noS = {}
     IN
     /\ {u.sndr : u \in ups} = outgoing[n]
     /\ IF incoming[n] = {}
          THEN \* source: only process the replies
               /\ incoming' = [incoming EXCEPT ![n] = noS]
               /\ outgoing' = [outgoing EXCEPT ![n] = outAfter]
               /\ mailbox' = [mailbox EXCEPT ![n] = @ \ ups]
               /\ UNCHANGED active
          ELSE \E k \in minS :
                 LET selfPrune == allYes /\ outAfter = {} /\ minS = incoming[n]
                     yesS      == IF allYes THEN minS ELSE {}
                     pruneS    == IF ~allYes THEN {}
                                  ELSE IF selfPrune THEN minS
                                  ELSE minS \ {k}
                     noIn      == incoming[n] \ yesS
                 IN
                 /\ mailbox' =
                      [m \in Nodes |->
                         IF m = n THEN mailbox[n] \ (ups \cup downs)
                         ELSE IF m \in incoming[n]
                           THEN mailbox[m] \cup
                                  {UpMsg(n, IF m \in yesS THEN "yes" ELSE "no",
                                         m \in pruneS)}
                           ELSE mailbox[m]]
                 /\ incoming' = [incoming EXCEPT
                                   ![n] = (incoming[n] \ (noIn \cup pruneS)) \cup noS]
                 /\ outgoing' = [outgoing EXCEPT ![n] = outAfter \cup noIn]
                 /\ active' = [active EXCEPT ![n] = ~selfPrune]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A n \in Nodes : WF_vars(Down(n)) /\ WF_vars(Up(n))

-----------------------------------------------------------------------------
(* Pending replies: a reversal or a pruning of edge {s, r} that sender s  *)
(* has already applied and receiver r has not yet processed.               *)
PendingRev(s, r) ==
  \E msg \in mailbox[r] : msg.phase = "up" /\ msg.sndr = s /\ msg.reply = "no"

PendingPrune(s, r) ==
  \E msg \in mailbox[r] : msg.phase = "up" /\ msg.sndr = s /\ msg.prune

(* Neighborhood invariant: the views of both endpoints of an edge agree,  *)
(* up to reversals or prunings that are still pending.                     *)
NeighborInv ==
  \A n, m \in Nodes :
    /\ m \in outgoing[n] <=>
         \/ n \in incoming[m]
         \/ PendingPrune(m, n)
         \/ PendingRev(m, n)
         \/ PendingRev(n, m)
    /\ (incoming[n] \cup outgoing[n]) \subseteq Neighbors(n)
    /\ incoming[n] \cap outgoing[n] = {}
    /\ n \notin incoming[n] \cup outgoing[n]

(* At most one pending message of each kind from the same neighbor. *)
MailboxOK ==
  \A n, s \in Nodes, p \in {"down", "up"} :
    Cardinality({msg \in mailbox[n] : msg.sndr = s /\ msg.phase = p}) <= 1

(* Inactive nodes have no remaining links. *)
InactiveIsolated ==
  \A n \in Nodes : ~active[n] => incoming[n] = {} /\ outgoing[n] = {}

IsLeader(n) == active[n] /\ incoming[n] = {} /\ outgoing[n] = {}

(* No two nodes simultaneously consider themselves leader. *)
LeaderSafety == \A l1, l2 \in Nodes : IsLeader(l1) /\ IsLeader(l2) => l1 = l2

(* Final configuration: the minimum node is the only active node. It has *)
(* no remaining links, and all mailboxes are empty.                        *)
Finished ==
  /\ \A n \in Nodes : active[n] <=> n = MinNode
  /\ IsLeader(MinNode)
  /\ \A n \in Nodes : mailbox[n] = {}

(* The only deadlock states are final leader states. *)
DeadlockOnlyFinal == (~ENABLED Next) => Finished

(* Finished states are quiescent. *)
FinishedIsQuiescent == Finished => ~ENABLED Next

-----------------------------------------------------------------------------
(* Liveness: from every initial state the algorithm terminates and stays *)
(* terminated.                                                             *)
Termination == <>[]Finished

EventuallyFinished == <>Finished

THEOREM Spec => [](TypeOK /\ NeighborInv /\ MailboxOK /\ InactiveIsolated
                   /\ LeaderSafety /\ DeadlockOnlyFinal)
THEOREM Spec => Termination
=============================================================================