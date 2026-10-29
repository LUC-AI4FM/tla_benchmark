---------------------------- MODULE YoYoPruning ----------------------------
(***************************************************************************)
(* Yo-Yo leader election on a connected undirected graph, with pruning so  *)
(* that the algorithm terminates. Edges are initially oriented from the    *)
(* smaller to the larger node. Sources start a "down" phase that           *)
(* propagates minimal values along edges. The "up" phase replies yes/no,   *)
(* reversing edges on "no" and pruning redundant edges and leaf sinks.     *)
(* Eventually the smallest node is the only remaining active node, and it  *)
(* has no remaining edges: it is the leader.                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE Reach(_)
Reach(S) == LET T == S \cup UNION {Neighbors(m) : m \in S}
            IN  IF T = S THEN S ELSE Reach(T)

IsConnected == \A n \in Nodes : Reach({n}) = Nodes

ASSUME
  /\ Nodes \subseteq Nat
  /\ Nodes # {}
  /\ Edges \subseteq {{m, n} : m, n \in Nodes}
  /\ \A e \in Edges : Cardinality(e) = 2
  /\ IsConnected

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES
  active,    \* active[n] is FALSE once n has been pruned
  phase,     \* "down" or "up"
  incoming,  \* incoming[n]: neighbors with edges oriented towards n
  outgoing,  \* outgoing[n]: neighbors with edges oriented away from n
  mailbox    \* mailbox[n]: set of messages sent to n, not yet consumed

vars == <<active, phase, incoming, outgoing, mailbox>>

DownMsg == [phase : {"down"}, sndr : Nodes, val : Nodes]
UpMsg   == [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]
Messages == DownMsg \cup UpMsg

kind(n) ==
  IF incoming[n] = {} /\ outgoing[n] = {} THEN "isolated"
  ELSE IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

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
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

\* Down messages from current incoming neighbors, up messages from current
\* outgoing neighbors.
DownMsgs(n) == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
UpMsgs(n)   == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

(***************************************************************************)
(* Down phase of a source: send own identity along all outgoing edges.     *)
(***************************************************************************)
DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] = {}
  /\ outgoing[n] # {}
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n]
                   THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> n]}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(***************************************************************************)
(* Down phase of an internal node or sink: once values from all incoming   *)
(* neighbors are received, forward their minimum along outgoing edges.     *)
(***************************************************************************)
DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ {msg.sndr : msg \in DownMsgs(n)} = incoming[n]
  /\ LET mv == Min({msg.val : msg \in DownMsgs(n)})
     IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n]
                       THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> mv]}
                       ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(***************************************************************************)
(* Up phase: once replies from all outgoing neighbors are received, reply  *)
(* to incoming neighbors, reverse edges on "no", prune redundant edges,    *)
(* and prune a sink that receives only a single value (a leaf).            *)
(***************************************************************************)
Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ LET dm == DownMsgs(n)
         um == UpMsgs(n)
     IN
     /\ {msg.sndr : msg \in dm} = incoming[n]
     /\ {msg.sndr : msg \in um} = outgoing[n]
     /\ LET vals    == {msg.val : msg \in dm}
            minVal  == IF incoming[n] = {} THEN n ELSE Min(vals)
            ValOf(s) == (CHOOSE msg \in dm : msg.sndr = s).val
            anyNo   == \E msg \in um : msg.reply = "no"
            prunedOut == {msg.sndr : msg \in {x \in um : x.prune}}
            noFrom  == {msg.sndr : msg \in {x \in um : x.reply = "no"}}
            isLeaf  == /\ outgoing[n] = {}
                       /\ incoming[n] # {}
                       /\ Cardinality(vals) = 1
            Keep(v) == Min({s \in incoming[n] : ValOf(s) = v})
            Pr(s)   == isLeaf \/ s # Keep(ValOf(s))
            Yes(s)  == ~anyNo /\ ValOf(s) = minVal
            Reply(s) == [phase |-> "up", sndr |-> n,
                         reply |-> IF Yes(s) THEN "yes" ELSE "no",
                         prune |-> Pr(s)]
            remOut  == outgoing[n] \ prunedOut
        IN
        /\ incoming' = [incoming EXCEPT ![n] =
                          {s \in incoming[n] : ~Pr(s) /\ Yes(s)}
                          \cup {s \in remOut : s \in noFrom}]
        /\ outgoing' = [outgoing EXCEPT ![n] =
                          {s \in incoming[n] : ~Pr(s) /\ ~Yes(s)}
                          \cup {s \in remOut : s \notin noFrom}]
        /\ active' = [active EXCEPT ![n] = ~isLeaf]
        /\ mailbox' = [m \in Nodes |->
                         IF m \in incoming[n] THEN mailbox[m] \cup {Reply(m)}
                         ELSE IF m = n THEN mailbox[n] \ (dm \cup um)
                         ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : DownSource(n) \/ DownOther(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

Leader == Min(Nodes)

Terminated ==
  /\ \A n \in Nodes \ {Leader} : ~active[n]
  /\ active[Leader]
  /\ incoming[Leader] = {}
  /\ outgoing[Leader] = {}

\* Each node's view of its edges is consistent with the underlying graph.
EdgesConsistent ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] \subseteq Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

\* Pruned nodes have no remaining edges.
InactiveIsolated ==
  \A n \in Nodes : ~active[n] => incoming[n] = {} /\ outgoing[n] = {}

\* The smallest node is never pruned.
LeaderActive == active[Leader]

\* When both endpoints are quiescent, they agree on the orientation of edges.
QuiescentAgreement ==
  \A m, n \in Nodes :
     (/\ phase[m] = "down" /\ phase[n] = "down"
      /\ mailbox[m] = {} /\ mailbox[n] = {})
     => (n \in outgoing[m] <=> m \in incoming[n])

\* Only the smallest node can be an isolated active node.
OnlyLeaderIsolated ==
  \A n \in Nodes : (active[n] /\ kind(n) = "isolated") => n = Leader

-----------------------------------------------------------------------------
(* Liveness / termination properties *)

Termination == <>Terminated

DeadlockIffTerminated == [](~(ENABLED Next) <=> Terminated)

=============================================================================