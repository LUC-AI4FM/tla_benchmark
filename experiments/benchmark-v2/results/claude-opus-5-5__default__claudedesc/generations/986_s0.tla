------------------------------ MODULE YoYoPruning ------------------------------
(***************************************************************************)
(* Yo-Yo leader election with pruning on an undirected connected graph.    *)
(* Nodes are unique integers. Edges are initially oriented from the        *)
(* smaller to the larger identity. Rounds alternate between a "down"       *)
(* phase, in which sources broadcast their identity and other nodes        *)
(* forward the minimum value received, and an "up" phase, in which nodes   *)
(* reply "yes" or "no" and the graph is pruned.                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Edges

ASSUME /\ Nodes \subseteq Int
       /\ Nodes # {}
       /\ Edges \subseteq {e \in SUBSET Nodes : Cardinality(e) = 2}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

VARIABLES active, phase, incoming, outgoing, mailbox

vars == <<active, phase, incoming, outgoing, mailbox>>

Messages ==
     [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]

DownMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
UpMsg(s, r, p) == [phase |-> "up", sndr |-> s, reply |-> r, prune |-> p]

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

(* down messages from current incoming neighbors *)
DownMsgs(n) == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
(* up messages from current outgoing neighbors *)
UpMsgs(n) == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

Val(n, k) == (CHOOSE msg \in DownMsgs(n) : msg.sndr = k).val
ReplyOf(n, o) == CHOOSE msg \in UpMsgs(n) : msg.sndr = o

(***************************************************************************)
(* Down phase                                                              *)
(***************************************************************************)
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

DownInternal(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ outgoing[n] # {}
  /\ {msg.sndr : msg \in DownMsgs(n)} = incoming[n]
  /\ LET mn == Min({msg.val : msg \in DownMsgs(n)})
     IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n] THEN mailbox[m] \cup {DownMsg(n, mn)}
                       ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* A sink receives all values and immediately replies. Among neighbors     *)
(* that sent the same value only one link is kept; if only one neighbor    *)
(* remains, the sink asks it to prune the link and becomes inactive.       *)
Sink(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ outgoing[n] = {}
  /\ {msg.sndr : msg \in DownMsgs(n)} = incoming[n]
  /\ LET dm   == DownMsgs(n)
         vals == {msg.val : msg \in dm}
         mn   == Min(vals)
         rep(v) == Min({k \in incoming[n] : Val(n, k) = v})
         kept == {rep(v) : v \in vals}
         leaf == Cardinality(kept) = 1
         R(k) == IF Val(n, k) = mn THEN "yes" ELSE "no"
         P(k) == leaf \/ k \notin kept
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ dm
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup {UpMsg(n, R(m), P(m))}
                               ELSE mailbox[m]]
         /\ active' = [active EXCEPT ![n] = ~leaf]
         /\ incoming' = [incoming EXCEPT ![n] =
                           IF leaf THEN {} ELSE {k \in kept : R(k) = "yes"}]
         /\ outgoing' = [outgoing EXCEPT ![n] =
                           IF leaf THEN {} ELSE {k \in kept : R(k) = "no"}]
  /\ UNCHANGED phase

(***************************************************************************)
(* Up phase                                                                *)
(***************************************************************************)
UpSource(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] = {}
  /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
  /\ LET um        == UpMsgs(n)
         prunedOut == {o \in outgoing[n] : ReplyOf(n, o).prune}
         noOut     == {o \in outgoing[n] \ prunedOut : ReplyOf(n, o).reply = "no"}
         yesOut    == outgoing[n] \ (prunedOut \cup noOut)
     IN  /\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ um]
         /\ incoming' = [incoming EXCEPT ![n] = noOut]
         /\ outgoing' = [outgoing EXCEPT ![n] = yesOut]
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ UNCHANGED active

UpInternal(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] # {}
  /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
  /\ LET dm    == DownMsgs(n)
         um    == UpMsgs(n)
         vals  == {msg.val : msg \in dm}
         mn    == Min(vals)
         rep(v) == Min({k \in incoming[n] : Val(n, k) = v})
         kept  == {rep(v) : v \in vals}
         anyNo == \E msg \in um : msg.reply = "no"
         R(k)  == IF ~anyNo /\ Val(n, k) = mn THEN "yes" ELSE "no"
         P(k)  == k \notin kept
         prunedOut == {o \in outgoing[n] : ReplyOf(n, o).prune}
         noOut     == {o \in outgoing[n] \ prunedOut : ReplyOf(n, o).reply = "no"}
         yesOut    == outgoing[n] \ (prunedOut \cup noOut)
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ (dm \cup um)
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup {UpMsg(n, R(m), P(m))}
                               ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] =
                           {k \in kept : R(k) = "yes"} \cup noOut]
         /\ outgoing' = [outgoing EXCEPT ![n] =
                           {k \in kept : R(k) = "no"} \cup yesOut]
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ UNCHANGED active

Next ==
  \E n \in Nodes :
     \/ DownSource(n)
     \/ DownInternal(n)
     \/ Sink(n)
     \/ UpSource(n)
     \/ UpInternal(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A n \in Nodes :
        /\ WF_vars(DownSource(n))
        /\ WF_vars(DownInternal(n))
        /\ WF_vars(Sink(n))
        /\ WF_vars(UpSource(n))
        /\ WF_vars(UpInternal(n))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
NeighborInv ==
  \A m, n \in Nodes :
     /\ incoming[n] \cap outgoing[n] = {}
     /\ incoming[n] \cup outgoing[n] \subseteq Neighbors(n)
     /\ ~active[n] => incoming[n] = {} /\ outgoing[n] = {}
     /\ m \in outgoing[n] =>
          \/ n \in incoming[m]
          \/ \E msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr = m
     /\ m \in incoming[n] =>
          \/ n \in outgoing[m]
          \/ \E msg \in mailbox[m] : msg.phase = "up" /\ msg.sndr = n

Terminated ==
  /\ \A n \in Nodes : active[n] <=> n = Min(Nodes)
  /\ incoming[Min(Nodes)] = {}
  /\ outgoing[Min(Nodes)] = {}

Liveness == <>Terminated

FinishIffTerminated == ~(ENABLED Next) <=> Terminated

(* Used as an invariant to produce traces showing source elimination. *)
MoreThanOneSource ==
  \E s1, s2 \in Nodes :
     /\ s1 # s2
     /\ active[s1] /\ active[s2]
     /\ incoming[s1] = {} /\ incoming[s2] = {}

THEOREM Spec => []TypeOK
THEOREM Spec => []NeighborInv
THEOREM Spec => []FinishIffTerminated
THEOREM Spec => Liveness
================================================================================