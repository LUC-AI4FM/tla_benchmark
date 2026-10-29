------------------------------- MODULE YoYoNoPruning -------------------------------
(***************************************************************************)
(* Yo-Yo leader election on an undirected connected graph (no pruning).    *)
(* Edges are oriented from smaller to larger identifiers.  Each round has  *)
(* a "down" phase, which propagates minimal ids along oriented edges, and  *)
(* an "up" phase, in which yes/no replies flow back.  An edge is reversed  *)
(* whenever a "no" is sent along it.  The sender reverses its view of the  *)
(* edge immediately.  The receiver reverses its view when it consumes the  *)
(* message.  Pruning can be added in a separate variant module.            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

ASSUME /\ Nodes \subseteq Int
       /\ Nodes # {}
       /\ Edges \subseteq SUBSET Nodes
       /\ \A e \in Edges : Cardinality(e) = 2

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

Messages ==
     [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

DownMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
UpMsg(s, r)   == [phase |-> "up", sndr |-> s, reply |-> r]

TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ \A n \in Nodes : incoming[n] \cup outgoing[n] \subseteq Neighbors(n)
  /\ mailbox \in [Nodes -> SUBSET Messages]

-----------------------------------------------------------------------------
Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

\* Down messages received by n in the current round from its incoming neighbors.
RcvdDown(n) ==
  {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}

\* Up replies received by n.
RcvdUp(n) == {msg \in mailbox[n] : msg.phase = "up"}

(***************************************************************************)
(* Down phase.  A source sends its own id.  A non-source waits for values  *)
(* from all incoming neighbors and forwards the minimum.  A sink has no    *)
(* outgoing neighbors, so it sends nothing.                                *)
(***************************************************************************)
Down(n) ==
  /\ phase[n] = "down"
  /\ {msg.sndr : msg \in RcvdDown(n)} = incoming[n]
  /\ LET v == IF incoming[n] = {} THEN n
              ELSE Min({msg.val : msg \in RcvdDown(n)})
     IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n]
                       THEN mailbox[m] \cup {DownMsg(n, v)}
                       ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(***************************************************************************)
(* Up phase.  The node waits for replies from all outgoing neighbors (a    *)
(* sink has none).  If any reply is "no", it sends "no" to every incoming  *)
(* neighbor.  Otherwise it sends "yes" to the neighbors that sent the      *)
(* minimum and "no" to the others.  A source has no incoming neighbors,    *)
(* so it sends nothing.  Every edge on which a "no" is sent or received is *)
(* reversed.                                                               *)
(***************************************************************************)
Up(n) ==
  /\ phase[n] = "up"
  /\ {msg.sndr : msg \in RcvdUp(n)} = outgoing[n]
  /\ LET D     == RcvdDown(n)
         U     == RcvdUp(n)
         noOut == {msg.sndr : msg \in {u \in U : u.reply = "no"}}
         minV  == IF D = {} THEN n ELSE Min({msg.val : msg \in D})
         noIn  == IF noOut # {} THEN incoming[n]
                  ELSE {msg.sndr : msg \in {d \in D : d.val # minV}}
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ (D \cup U)
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup
                                      {UpMsg(n, IF m \in noIn THEN "no" ELSE "yes")}
                               ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] = (@ \ noIn) \cup noOut]
         /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noOut) \cup noIn]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Node(n) == Down(n) \/ Up(n)

Next == \E n \in Nodes : Node(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Node(n))

-----------------------------------------------------------------------------
(* Properties *)

NoMsg(from, to) == UpMsg(from, "no") \in mailbox[to]

\* Each edge is either consistently oriented with no pending "no" message, or
\* it is being reversed: both endpoints see it as outgoing, and exactly one
\* "no" message is in flight along it.
NeighborInv ==
  \A m, n \in Nodes : {m, n} \in Edges =>
    \/ /\ m \in outgoing[n] /\ n \in incoming[m]
       /\ m \notin incoming[n] /\ n \notin outgoing[m]
       /\ ~NoMsg(m, n) /\ ~NoMsg(n, m)
    \/ /\ n \in outgoing[m] /\ m \in incoming[n]
       /\ n \notin incoming[m] /\ m \notin outgoing[n]
       /\ ~NoMsg(m, n) /\ ~NoMsg(n, m)
    \/ /\ m \in outgoing[n] /\ n \in outgoing[m]
       /\ m \notin incoming[n] /\ n \notin incoming[m]
       /\ NoMsg(m, n) # NoMsg(n, m)

Sources == {n \in Nodes : incoming[n] = {}}

\* The node with the smallest id always remains a source.
MinIsSource == MinNode \in Sources

\* No new sources are ever created.
NoNewSource ==
  [][\A n \in Nodes : incoming'[n] = {} => incoming[n] = {}]_vars

Stabilized ==
  /\ Sources = {MinNode}
  /\ \A n \in Nodes : \A msg \in mailbox[n] :
        /\ msg.phase = "down" => msg.val = MinNode
        /\ msg.phase = "up" => msg.reply = "yes"

\* Eventually only the smallest-id node is a source.
EventuallyUniqueSource == <>[](Sources = {MinNode})

Liveness == <>[]Stabilized

=============================================================================