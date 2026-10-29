------------------------------ MODULE YoYoNoPruning ------------------------------
(***************************************************************************)
(* Yo-Yo leader election on an arbitrary undirected, connected graph       *)
(* without self-loops, modelled without graph pruning.                     *)
(***************************************************************************)
EXTENDS TLC, Integers, FiniteSets

CONSTANTS Nodes, Edges

ASSUME /\ Nodes \subseteq Int
       /\ Nodes # {}
       /\ \A e \in Edges : e \subseteq Nodes /\ Cardinality(e) = 2

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

Messages ==
     [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

DownMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
UpMsg(s, r)   == [phase |-> "up", sndr |-> s, reply |-> r]

kind(n) == IF incoming[n] = {} THEN "source"
           ELSE IF outgoing[n] = {} THEN "sink"
           ELSE "internal"

(* down messages from current upstream neighbors *)
DownMsgs(n) == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
(* up messages from current downstream neighbors *)
UpMsgs(n) == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

-----------------------------------------------------------------------------
TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]
  /\ \A n \in Nodes :
       /\ incoming[n] \cup outgoing[n] = Neighbors(n)
       /\ incoming[n] \cap outgoing[n] = {}
       /\ \A msg \in mailbox[n] : msg.sndr \in Neighbors(n)

Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

-----------------------------------------------------------------------------
(* Downward phase: once values from all upstream neighbors have arrived    *)
(* (immediately for sources), forward the minimum (own id for sources).    *)
Down(n) ==
  /\ phase[n] = "down"
  /\ \A m \in incoming[n] : \E msg \in DownMsgs(n) : msg.sndr = m
  /\ LET v == IF incoming[n] = {} THEN n
              ELSE Min({msg.val : msg \in DownMsgs(n)})
     IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n]
                       THEN mailbox[m] \cup {DownMsg(n, v)}
                       ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(* Upward phase: once replies from all downstream neighbors have arrived   *)
(* (immediately for sinks), answer upstream neighbors and reverse edges    *)
(* carrying "no".                                                          *)
Up(n) ==
  /\ phase[n] = "up"
  /\ \A m \in outgoing[n] : \E msg \in UpMsgs(n) : msg.sndr = m
  /\ LET dmsgs   == DownMsgs(n)
         umsgs   == UpMsgs(n)
         noSndrs == {msg.sndr : msg \in {u \in umsgs : u.reply = "no"}}
         allYes  == noSndrs = {}
         minv    == Min({msg.val : msg \in dmsgs})
         yesTo   == IF allYes /\ dmsgs # {}
                    THEN {msg.sndr : msg \in {d \in dmsgs : d.val = minv}}
                    ELSE {}
         noTo    == incoming[n] \ yesTo
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ (dmsgs \cup umsgs)
                          ELSE IF m \in yesTo THEN mailbox[m] \cup {UpMsg(n, "yes")}
                          ELSE IF m \in noTo THEN mailbox[m] \cup {UpMsg(n, "no")}
                          ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] = (incoming[n] \ noTo) \cup noSndrs]
         /\ outgoing' = [outgoing EXCEPT ![n] = (outgoing[n] \ noSndrs) \cup noTo]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Down(n) \/ Up(n))

-----------------------------------------------------------------------------
(* Edge orientation is consistent, modulo in-flight "no" messages.         *)
NoMsgFrom(s, r) == \E msg \in mailbox[r] : msg.phase = "up" /\ msg.sndr = s /\ msg.reply = "no"

NeighborInv ==
  \A m, n \in Nodes : {m, n} \in Edges =>
     \/ m \in outgoing[n] /\ n \in incoming[m]
     \/ n \in outgoing[m] /\ m \in incoming[n]
     \/ /\ m \in outgoing[n] /\ n \in outgoing[m]
        /\ NoMsgFrom(n, m) \/ NoMsgFrom(m, n)

(* No node ever becomes a source. *)
NoNewSource ==
  [][\A n \in Nodes : incoming'[n] = {} => incoming[n] = {}]_vars

Sources == {n \in Nodes : incoming[n] = {}}

Stable ==
  /\ Sources = {MinNode}
  /\ \A n \in Nodes : \A msg \in mailbox[n] :
        /\ msg.phase = "down" => msg.val = MinNode
        /\ msg.phase = "up" => msg.reply = "yes"

Liveness == <>[]Stable

MoreThanOneSource == Cardinality(Sources) > 1

SingleSourceEventually == MoreThanOneSource ~> (Cardinality(Sources) = 1)
=============================================================================