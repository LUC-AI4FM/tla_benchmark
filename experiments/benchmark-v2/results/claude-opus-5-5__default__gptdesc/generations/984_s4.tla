---------------------------- MODULE YoYoPruning ----------------------------
(***************************************************************************)
(* Yo-Yo leader election with pruning on an undirected, loop-free,         *)
(* connected graph over a fixed set of numbered nodes.  The initial graph  *)
(* is chosen nondeterministically among all connected graphs over Nodes,   *)
(* and each edge is oriented from the smaller to the larger endpoint.      *)
(* Nodes then alternate between down and up phases, exchanging messages,   *)
(* reversing and pruning edges, and deactivating, until a single active    *)
(* node (the leader) without neighbors remains.                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT Nodes
ASSUME NodesAssump == Nodes \subseteq Nat /\ Nodes # {} /\ IsFiniteSet(Nodes)

VARIABLES
  active,    \* active[n] : is node n still participating?
  phase,     \* phase[n] \in {"down", "up"}
  incoming,  \* incoming[n] : set of in-neighbors of n (as seen by n)
  outgoing,  \* outgoing[n] : set of out-neighbors of n (as seen by n)
  mailbox    \* mailbox[n] : set of messages received by n

vars == <<active, phase, incoming, outgoing, mailbox>>

-----------------------------------------------------------------------------
(* Auxiliary definitions *)

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

PossibleEdges == { {m, n} : m, n \in Nodes } \ { {n} : n \in Nodes }

RECURSIVE Reach(_, _)
Reach(S, E) ==
  LET S2 == S \cup { m \in Nodes : \E k \in S : {k, m} \in E }
  IN  IF S2 = S THEN S ELSE Reach(S2, E)

IsConnected(E) == \A n \in Nodes : Reach({n}, E) = Nodes

Neighbors(n) == incoming[n] \cup outgoing[n]

downMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s, r, p) == [phase |-> "up", sndr |-> s, reply |-> r, prune |-> p]

Messages ==
     [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ active = [n \in Nodes |-> TRUE]
  /\ phase = [n \in Nodes |-> "down"]
  /\ \E E \in SUBSET PossibleEdges :
        /\ IsConnected(E)
        /\ incoming = [n \in Nodes |-> {m \in Nodes : {m, n} \in E /\ m < n}]
        /\ outgoing = [n \in Nodes |-> {m \in Nodes : {m, n} \in E /\ n < m}]
  /\ mailbox = [n \in Nodes |-> {}]

-----------------------------------------------------------------------------
(* Down phase *)

\* A source sends its own identity to all out-neighbors.
DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ Neighbors(n) # {}
  /\ incoming[n] = {}
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n]
                   THEN mailbox[m] \cup {downMsg(n, n)}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

\* A non-source waits for values from all in-neighbors and forwards the minimum.
DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ LET dMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
     IN  /\ {msg.sndr : msg \in dMsgs} = incoming[n]
         /\ LET v == Min({msg.val : msg \in dMsgs})
            IN  mailbox' = [m \in Nodes |->
                              IF m \in outgoing[n]
                              THEN mailbox[m] \cup {downMsg(n, v)}
                              ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

-----------------------------------------------------------------------------
(* Up phase *)

\* A node waits for replies from all out-neighbors, then replies to its
\* in-neighbors, reverses edges for "no" replies, prunes edges, and
\* possibly deactivates.
Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ Neighbors(n) # {}
  /\ LET uMsgs == {msg \in mailbox[n] : msg.phase = "up"}
     IN  {msg.sndr : msg \in uMsgs} = outgoing[n]
  /\ LET dMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
         uMsgs == {msg \in mailbox[n] : msg.phase = "up"}
         valOf(i) == (CHOOSE msg \in dMsgs : msg.sndr = i).val
         vals == {valOf(i) : i \in incoming[n]}
         minVal == IF vals = {} THEN n ELSE Min(vals)
         noRcvd == \E msg \in uMsgs : msg.reply = "no"
         outPruned == {msg.sndr : msg \in {u \in uMsgs : u.prune}}
         outReversed == {msg.sndr : msg \in {u \in uMsgs : u.reply = "no" /\ ~u.prune}}
         outKept == outgoing[n] \ (outPruned \cup outReversed)
         keep(i) == i = Min({j \in incoming[n] : valOf(j) = valOf(i)})
         selfPrune == /\ incoming[n] # {}
                      /\ outKept \cup outReversed = {}
                      /\ Cardinality(vals) = 1
         pruneIn(i) == selfPrune \/ ~keep(i)
         replyYes(i) == ~noRcvd /\ valOf(i) = minVal
         inPruned == {i \in incoming[n] : pruneIn(i)}
         inReversed == {i \in incoming[n] : ~pruneIn(i) /\ ~replyYes(i)}
         inKept == incoming[n] \ (inPruned \cup inReversed)
         newIn == inKept \cup outReversed
         newOut == outKept \cup inReversed
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m = n
                          THEN mailbox[n] \ (dMsgs \cup uMsgs)
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup
                                      {upMsg(n, IF replyYes(m) THEN "yes" ELSE "no",
                                             pruneIn(m))}
                               ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] = newIn]
         /\ outgoing' = [outgoing EXCEPT ![n] = newOut]
         /\ active' = [active EXCEPT ![n] =
                          (newIn \cup newOut # {}) \/ (incoming[n] = {})]
  /\ phase' = [phase EXCEPT ![n] = "down"]

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next == \E n \in Nodes : DownSource(n) \/ DownOther(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

NoSelfLoops == \A n \in Nodes : n \notin Neighbors(n)

InOutDisjoint == \A n \in Nodes : incoming[n] \cap outgoing[n] = {}

InactiveIsolated == \A n \in Nodes : ~active[n] => Neighbors(n) = {}

SomeActive == \E n \in Nodes : active[n]

MinNodeIsActiveSource ==
  /\ active[Min(Nodes)]
  /\ incoming[Min(Nodes)] = {}

Terminated ==
  \E l \in Nodes :
     /\ active[l]
     /\ Neighbors(l) = {}
     /\ \A n \in Nodes \ {l} : ~active[n]

LeaderIsMin == Terminated => \A n \in Nodes : active[n] <=> n = Min(Nodes)

Invariants ==
  /\ TypeOK
  /\ NoSelfLoops
  /\ InOutDisjoint
  /\ InactiveIsolated
  /\ SomeActive
  /\ MinNodeIsActiveSource
  /\ LeaderIsMin

-----------------------------------------------------------------------------
(* Liveness and termination characterization *)

Liveness == <>Terminated

TerminationIsDeadlock == [](Terminated <=> ~ENABLED Next)

THEOREM Spec => []Invariants
THEOREM Spec => Liveness
THEOREM Spec => TerminationIsDeadlock
=============================================================================