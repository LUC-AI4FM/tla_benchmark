---------------------------- MODULE YoYoNoPruning ----------------------------
(***************************************************************************)
(* Yo-Yo leader election on an arbitrary connected undirected graph       *)
(* without self-loops (no pruning).                                        *)
(* Nodes are integers. The node with the smallest identifier becomes the   *)
(* unique source and therefore the leader.                                 *)
(* Each edge is oriented from the smaller to the larger identifier at the  *)
(* start. The orientation is kept locally at every node through the sets   *)
(* incoming[n] and outgoing[n].                                            *)
(* The down phase propagates the minimum identifiers from the sources      *)
(* toward the sinks.                                                       *)
(* The up phase propagates yes/no replies back toward the sources. Every   *)
(* edge on which a "no" is sent is reversed.                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE Reach(_)
Reach(S) ==
    LET T == S \cup {m \in Nodes : \E k \in S : {m, k} \in Edges}
    IN  IF T = S THEN S ELSE Reach(T)

IsConnected == \A n \in Nodes : Reach({n}) = Nodes

ASSUME /\ Nodes \subseteq Int
       /\ Nodes # {}
       /\ IsFiniteSet(Nodes)
       /\ Edges \subseteq {e \in SUBSET Nodes : Cardinality(e) = 2}  \* undirected, no self-loops
       /\ IsConnected

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

DownMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
UpMsg(s, r)   == [phase |-> "up", sndr |-> s, reply |-> r]

Messages ==
    [phase : {"down"}, sndr : Nodes, val : Nodes]
    \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

kind(n) ==
    IF incoming[n] = {} THEN "source"
    ELSE IF outgoing[n] = {} THEN "sink"
    ELSE "internal"

\* Down messages received from the current incoming neighbors.
DownMsgs(n) ==
    {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}

\* Up messages received from the current outgoing neighbors.
UpMsgs(n) ==
    {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

-----------------------------------------------------------------------------
Init ==
    /\ phase    = [n \in Nodes |-> "down"]
    /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
    /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
    /\ mailbox  = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase. A source sends its own identifier to all of its outgoing   *)
(* neighbors.                                                              *)
(***************************************************************************)
DownSource(n) ==
    /\ phase[n] = "down"
    /\ kind(n) = "source"
    /\ mailbox' = [m \in Nodes |->
                     IF m \in outgoing[n]
                     THEN mailbox[m] \cup {DownMsg(n, n)}
                     ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

(***************************************************************************)
(* Down phase. An internal node or a sink waits for values from all of its *)
(* incoming neighbors. It then forwards the minimum to all of its outgoing *)
(* neighbors. A sink has no outgoing neighbors, so it forwards nothing.    *)
(* The received down messages stay in the mailbox until the up phase.     *)
(***************************************************************************)
DownOther(n) ==
    /\ phase[n] = "down"
    /\ kind(n) # "source"
    /\ LET dMsgs  == DownMsgs(n)
       IN  /\ {msg.sndr : msg \in dMsgs} = incoming[n]
           /\ LET minVal == Min({msg.val : msg \in dMsgs})
              IN  mailbox' = [m \in Nodes |->
                                IF m \in outgoing[n]
                                THEN mailbox[m] \cup {DownMsg(n, minVal)}
                                ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

(***************************************************************************)
(* Up phase for a sink or an internal node.                                *)
(* The node first waits for replies from all of its outgoing neighbors.    *)
(* A sink has no outgoing neighbors, so it does not wait.                  *)
(* If every reply is "yes", the node sends "yes" to the senders of the     *)
(* minimum value and "no" to every other incoming neighbor.                *)
(* Otherwise the node sends "no" to all of its incoming neighbors.         *)
(* Every edge on which a "no" was sent or received is reversed.            *)
(***************************************************************************)
UpNonSource(n) ==
    /\ phase[n] = "up"
    /\ kind(n) # "source"
    /\ LET dMsgs == DownMsgs(n)
           uMsgs == UpMsgs(n)
       IN  /\ {msg.sndr : msg \in uMsgs} = outgoing[n]
           /\ LET minVal == Min({msg.val : msg \in dMsgs})
                  noFrom == {msg.sndr : msg \in {mm \in uMsgs : mm.reply = "no"}}
                  yesTo  == IF noFrom = {}
                            THEN {msg.sndr : msg \in {mm \in dMsgs : mm.val = minVal}}
                            ELSE {}
                  noTo   == incoming[n] \ yesTo
              IN  /\ mailbox' = [m \in Nodes |->
                                   IF m = n THEN mailbox[n] \ (dMsgs \cup uMsgs)
                                   ELSE IF m \in yesTo THEN mailbox[m] \cup {UpMsg(n, "yes")}
                                   ELSE IF m \in noTo  THEN mailbox[m] \cup {UpMsg(n, "no")}
                                   ELSE mailbox[m]]
                  /\ incoming' = [incoming EXCEPT ![n] = (@ \ noTo) \cup noFrom]
                  /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noFrom) \cup noTo]
    /\ phase' = [phase EXCEPT ![n] = "down"]

(***************************************************************************)
(* Up phase for a source.                                                  *)
(* The source waits for replies from all of its outgoing neighbors.        *)
(* It then reverses the edges on which it received "no".                   *)
(***************************************************************************)
UpSource(n) ==
    /\ phase[n] = "up"
    /\ kind(n) = "source"
    /\ LET uMsgs  == UpMsgs(n)
           noFrom == {msg.sndr : msg \in {mm \in uMsgs : mm.reply = "no"}}
       IN  /\ {msg.sndr : msg \in uMsgs} = outgoing[n]
           /\ mailbox'  = [mailbox EXCEPT ![n] = @ \ uMsgs]
           /\ incoming' = [incoming EXCEPT ![n] = @ \cup noFrom]
           /\ outgoing' = [outgoing EXCEPT ![n] = @ \ noFrom]
    /\ phase' = [phase EXCEPT ![n] = "down"]

Step(n) ==
    \/ DownSource(n)
    \/ DownOther(n)
    \/ UpNonSource(n)
    \/ UpSource(n)

Next == \E n \in Nodes : Step(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Step(n))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK ==
    /\ phase    \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox  \in [Nodes -> SUBSET Messages]

\* At every node, the incoming and outgoing sets partition its neighbors.
NeighborInv ==
    \A n \in Nodes :
        /\ incoming[n] \cap outgoing[n] = {}
        /\ incoming[n] \cup outgoing[n] = Neighbors(n)

\* No new sources are created. Every current source was a source initially,
\* meaning it was smaller than all of its neighbors.
NoNewSource ==
    \A n \in Nodes :
        kind(n) = "source" => \A m \in Neighbors(n) : n < m

\* The minimum node is a source in every state.
MinIsSource == kind(MinNode) = "source"

(***************************************************************************)
(* Liveness property                                                       *)
(***************************************************************************)
AllUpYes ==
    \A n \in Nodes : \A msg \in mailbox[n] :
        msg.phase = "up" => msg.reply = "yes"

UniqueSource ==
    \A n \in Nodes : kind(n) = "source" <=> n = MinNode

Stabilization == <>[](UniqueSource /\ AllUpYes)

THEOREM Spec => [](TypeOK /\ NeighborInv /\ NoNewSource /\ MinIsSource)
THEOREM Spec => Stabilization
=============================================================================