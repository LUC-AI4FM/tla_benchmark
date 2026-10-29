------------------------------ MODULE MCYoYoNoPruning ------------------------------
(***************************************************************************)
(* Model-checking wrapper for the YoYo leader election algorithm without   *)
(* pruning. The algorithm is given as an inner module so that this file is *)
(* self-contained. It is instantiated below without substitutions, using a *)
(* fixed graph defined in this module.                                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC, TLCExt

---------------------------- MODULE YoYoNoPruning ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges

ASSUME
  /\ Nodes \subseteq Nat
  /\ Edges \subseteq SUBSET Nodes
  /\ \A e \in Edges : Cardinality(e) = 2

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES
  phase,     \* phase[n] \in {"down", "up"}
  incoming,  \* incoming[n]: neighbors with an edge oriented towards n
  outgoing,  \* outgoing[n]: neighbors with an edge oriented away from n
  mailbox    \* mailbox[n]: set of messages received by n

vars == <<phase, incoming, outgoing, mailbox>>

Messages ==
       [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

kind(n) ==
  IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

\* down messages of the current round: those sent by incoming neighbors
DownMsgs(n) == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
\* up messages of the current round: those sent by outgoing neighbors
UpMsgs(n) == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

DownSource(n) ==
  /\ phase[n] = "down"
  /\ kind(n) = "source"
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n]
                   THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> n]}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

DownInternal(n) ==
  /\ phase[n] = "down"
  /\ kind(n) = "internal"
  /\ {msg.sndr : msg \in DownMsgs(n)} = incoming[n]
  /\ LET v == Min({msg.val : msg \in DownMsgs(n)})
     IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n]
                       THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> v]}
                       ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

DownSink(n) ==
  /\ phase[n] = "down"
  /\ kind(n) = "sink"
  /\ {msg.sndr : msg \in DownMsgs(n)} = incoming[n]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing, mailbox>>

Up(n) ==
  /\ phase[n] = "up"
  /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
  /\ LET dmsgs    == DownMsgs(n)
         umsgs    == UpMsgs(n)
         noOut    == {u.sndr : u \in {x \in umsgs : x.reply = "no"}}
         minVal   == IF kind(n) = "source" THEN n
                     ELSE Min({d.val : d \in dmsgs})
         minSndrs == {d.sndr : d \in {x \in dmsgs : x.val = minVal}}
         yesIn    == IF noOut = {} THEN minSndrs ELSE {}
         noIn     == incoming[n] \ yesIn
         Answer(m) == IF m \in yesIn THEN "yes" ELSE "no"
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ (dmsgs \cup umsgs)
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup
                                      {[phase |-> "up", sndr |-> n, reply |-> Answer(m)]}
                               ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] = (@ \ noIn) \cup noOut]
         /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noOut) \cup noIn]
         /\ phase' = [phase EXCEPT ![n] = "down"]

Next ==
  \E n \in Nodes :
     \/ DownSource(n)
     \/ DownInternal(n)
     \/ DownSink(n)
     \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
==============================================================================