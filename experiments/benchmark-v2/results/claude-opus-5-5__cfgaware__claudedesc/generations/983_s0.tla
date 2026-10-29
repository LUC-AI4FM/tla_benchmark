------------------------------ MODULE MCYoYoPruning ------------------------------
(***************************************************************************)
(* Model-checking configuration for the Yo-Yo leader election algorithm   *)
(* with pruning, on a concrete undirected graph topology.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Small example graph: 5 nodes, 5 edges.                                  *)
(***************************************************************************)
Nodes == 1 .. 5
Edges == { {1,2}, {1,3}, {2,4}, {3,4}, {4,5} }

(***************************************************************************)
(* Larger alternative test case (11 nodes, 14 edges):                      *)
(* Nodes == 1 .. 11                                                        *)
(* Edges == { {1,2}, {1,3}, {2,4}, {3,4}, {4,5}, {5,6}, {5,7}, {6,8},      *)
(*            {7,8}, {8,9}, {9,10}, {9,11}, {10,11}, {2,6} }               *)
(***************************************************************************)

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Messages ==
  [kind : {"down", "up"}, sndr : Nodes, val : Nodes,
   reply : {"yes", "no"}, prune : BOOLEAN]

VARIABLES active, phase, incoming, outgoing, mailbox

vars == <<active, phase, incoming, outgoing, mailbox>>

-----------------------------------------------------------------------------
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

DownMsg(n, v) ==
  [kind |-> "down", sndr |-> n, val |-> v, reply |-> "yes", prune |-> FALSE]

UpMsg(n, r, p) ==
  [kind |-> "up", sndr |-> n, val |-> n, reply |-> r, prune |-> p]

DownMsgs(n) == {msg \in mailbox[n] : msg.kind = "down" /\ msg.sndr \in incoming[n]}
UpMsgs(n)   == {msg \in mailbox[n] : msg.kind = "up" /\ msg.sndr \in outgoing[n]}

-----------------------------------------------------------------------------
(* Down phase: a source sends its own identity to all outgoing neighbors. *)
DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] = {}
  /\ outgoing[n] # {}
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n] THEN mailbox[m] \cup {DownMsg(n, n)}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* Down phase: a non-source waits for values from all incoming neighbors *)
(* and forwards the minimum to its outgoing neighbors.                    *)
DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ {msg.sndr : msg \in DownMsgs(n)} = incoming[n]
  /\ LET v == Min({msg.val : msg \in DownMsgs(n)})
     IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n] THEN mailbox[m] \cup {DownMsg(n, v)}
                       ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* Up phase: once replies from all outgoing neighbors have arrived, the   *)
(* node replies to its incoming neighbors, prunes redundant edges, and    *)
(* flips edges for which "no" was sent or received.                       *)
Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
  /\ LET dmsgs == DownMsgs(n)
         umsgs == UpMsgs(n)
         vals == {msg.val : msg \in dmsgs}
         senders(v) == {msg.sndr : msg \in {x \in dmsgs : x.val = v}}
         valOf(m) == (CHOOSE msg \in dmsgs : msg.sndr = m).val
         kept == {Min(senders(v)) : v \in vals}
         pruned == incoming[n] \ kept
         anyNo == \E msg \in umsgs : msg.reply = "no" /\ ~msg.prune
         minVal == IF vals = {} THEN n ELSE Min(vals)
         reply(m) == IF ~anyNo /\ valOf(m) = minVal THEN "yes" ELSE "no"
         selfPrune == outgoing[n] = {} /\ Cardinality(kept) = 1
         prunedOut == {msg.sndr : msg \in {x \in umsgs : x.prune}}
         noOut == {msg.sndr : msg \in {x \in umsgs : x.reply = "no"}} \ prunedOut
         keptNo == {k \in kept : reply(k) = "no"}
         keptYes == {k \in kept : reply(k) = "yes"}
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ (dmsgs \cup umsgs)
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup
                                      {UpMsg(n, reply(m), m \in pruned \/ selfPrune)}
                               ELSE mailbox[m]]
         /\ IF selfPrune
              THEN /\ active' = [active EXCEPT ![n] = FALSE]
                   /\ incoming' = [incoming EXCEPT ![n] = {}]
                   /\ outgoing' = [outgoing EXCEPT ![n] = {}]
              ELSE /\ active' = active
                   /\ incoming' = [incoming EXCEPT ![n] = keptYes \cup noOut]
                   /\ outgoing' = [outgoing EXCEPT ![n] =
                                     (outgoing[n] \ (noOut \cup prunedOut)) \cup keptNo]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : DownSource(n) \/ DownOther(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Edge orientations are consistent between neighbors. *)
NeighborInv ==
  \A n \in Nodes :
     /\ incoming[n] \subseteq Neighbors(n)
     /\ outgoing[n] \subseteq Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}
     /\ \A m \in incoming[n] : n \in outgoing[m]

Finished ==
  \A n \in Nodes :
     active[n] => /\ incoming[n] = {}
                  /\ outgoing[n] = {}
                  /\ phase[n] = "down"

FinishIffTerminated == Finished <=> ~(ENABLED Next)

Liveness == <>Finished

(* Fails for the small example graph, hence not checked.                   *)
NoNewSource ==
  [][\A n \in Nodes : (incoming'[n] = {} /\ outgoing'[n] # {})
                         => incoming[n] = {}]_vars
=============================================================================