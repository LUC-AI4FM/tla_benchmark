------------------------------- MODULE YoYo -------------------------------
(***************************************************************************)
(* Yo-Yo leader election on an arbitrary connected undirected graph       *)
(* without self-loops. Nodes are integers, and the node with the smallest *)
(* identifier becomes the leader. Edges are oriented from the smaller to  *)
(* the larger identifier at the start. Nodes then alternate between a     *)
(* "down" phase and an "up" phase:                                        *)
(*   - In the down phase, minimum identifiers flow from sources to sinks. *)
(*   - In the up phase, yes/no replies flow back, and every edge that     *)
(*     carries a "no" reply is reversed.                                  *)
(* This version does no pruning.                                          *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

(***************************************************************************)
(* Graph helpers and assumptions about the input graph.                   *)
(***************************************************************************)
Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

ReachableFrom(n) ==
    LET RECURSIVE R(_)
        R(S) == LET S2 == S \cup {m \in Nodes : \E k \in S : {k, m} \in Edges}
                IN  IF S2 = S THEN S ELSE R(S2)
    IN  R({n})

ASSUME NodesAssumption ==
    /\ Nodes \subseteq Int
    /\ Nodes # {}
    /\ IsFiniteSet(Nodes)

ASSUME EdgesAssumption ==
    /\ Edges \subseteq SUBSET Nodes
    /\ \A e \in Edges : Cardinality(e) = 2          \* no self-loops

ASSUME ConnectedAssumption ==
    \A n \in Nodes : ReachableFrom(n) = Nodes      \* strongly connected

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

Messages ==
    [phase : {"down"}, sndr : Nodes, val : Nodes]
    \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

VARIABLES
    phase,      \* phase[n] \in {"down", "up"}
    incoming,   \* incoming[n] : neighbors whose edge points to n
    outgoing,   \* outgoing[n] : neighbors that n's edge points to
    mailbox     \* mailbox[n] : set of messages received by n

vars == <<phase, incoming, outgoing, mailbox>>

kind(n) ==
    IF incoming[n] = {} THEN "source"
    ELSE IF outgoing[n] = {} THEN "sink"
    ELSE "internal"

(***************************************************************************)
(* Initial state.                                                          *)
(***************************************************************************)
Init ==
    /\ phase = [n \in Nodes |-> "down"]
    /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
    /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
    /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Messages of the current round that are present at node n.              *)
(***************************************************************************)
DownMsgs(n) == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
UpMsgs(n)   == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

(***************************************************************************)
(* Down phase.                                                             *)
(***************************************************************************)
DownSource(n) ==
    /\ phase[n] = "down"
    /\ kind(n) = "source"
    /\ mailbox' = [m \in Nodes |->
                     IF m \in outgoing[n]
                     THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> n]}
                     ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

DownOther(n) ==
    /\ phase[n] = "down"
    /\ kind(n) \in {"internal", "sink"}
    /\ {msg.sndr : msg \in DownMsgs(n)} = incoming[n]
    /\ LET min == Min({msg.val : msg \in DownMsgs(n)})
       IN  mailbox' = [m \in Nodes |->
                         IF m \in outgoing[n]
                         THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> min]}
                         ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

(***************************************************************************)
(* Up phase.                                                               *)
(***************************************************************************)
UpSource(n) ==
    /\ phase[n] = "up"
    /\ kind(n) = "source"
    /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
    /\ LET noSndrs == {msg.sndr : msg \in {mm \in UpMsgs(n) : mm.reply = "no"}}
       IN  /\ incoming' = [incoming EXCEPT ![n] = noSndrs]
           /\ outgoing' = [outgoing EXCEPT ![n] = outgoing[n] \ noSndrs]
    /\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ UpMsgs(n)]
    /\ phase' = [phase EXCEPT ![n] = "down"]

UpOther(n) ==
    /\ phase[n] = "up"
    /\ kind(n) \in {"internal", "sink"}
    /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
    /\ LET downMsgs == DownMsgs(n)
           upMsgs   == UpMsgs(n)
           noSndrs  == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
           min      == Min({msg.val : msg \in downMsgs})
           minSndrs == {msg.sndr : msg \in {mm \in downMsgs : mm.val = min}}
           \* the incoming neighbors that receive a "no"
           noRcvrs  == IF noSndrs # {} THEN incoming[n]
                       ELSE incoming[n] \ minSndrs
       IN  /\ mailbox' = [m \in Nodes |->
                IF m \in incoming[n]
                THEN mailbox[m] \cup {[phase |-> "up", sndr |-> n,
                                       reply |-> IF m \in noRcvrs THEN "no" ELSE "yes"]}
                ELSE IF m = n THEN mailbox[n] \ (downMsgs \cup upMsgs)
                ELSE mailbox[m]]
           /\ incoming' = [incoming EXCEPT ![n] = (incoming[n] \ noRcvrs) \cup noSndrs]
           /\ outgoing' = [outgoing EXCEPT ![n] = (outgoing[n] \ noSndrs) \cup noRcvrs]
    /\ phase' = [phase EXCEPT ![n] = "down"]

NodeStep(n) ==
    \/ DownSource(n)
    \/ DownOther(n)
    \/ UpSource(n)
    \/ UpOther(n)

Next == \E n \in Nodes : NodeStep(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(NodeStep(n))

(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)
TypeOK ==
    /\ phase \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox \in [Nodes -> SUBSET Messages]

\* Every neighbor is either incoming or outgoing, never both. Two nodes
\* can disagree about the direction of an edge only while a "no" reply
\* is in transit. Both nodes can never see the edge as incoming.
NeighborInv ==
    \A n \in Nodes :
        /\ incoming[n] \cup outgoing[n] = Neighbors(n)
        /\ incoming[n] \cap outgoing[n] = {}
        /\ \A m \in Neighbors(n) :
              /\ ~ (m \in incoming[n] /\ n \in incoming[m])
              /\ (m \in outgoing[n] /\ n \in outgoing[m]) =>
                    \/ [phase |-> "up", sndr |-> m, reply |-> "no"] \in mailbox[n]
                    \/ [phase |-> "up", sndr |-> n, reply |-> "no"] \in mailbox[m]

\* No node that is not currently a source becomes a source.
NoNewSource ==
    [][\A n \in Nodes : kind(n)' = "source" => kind(n) = "source"]_vars

(***************************************************************************)
(* Liveness: eventually the minimum node is the only source, and every    *)
(* up message is "yes".                                                    *)
(***************************************************************************)
Stabilization ==
    <>[] /\ \A n \in Nodes : kind(n) = "source" <=> n = MinNode
         /\ \A n \in Nodes : \A msg \in mailbox[n] :
               msg.phase = "up" => msg.reply = "yes"

THEOREM Spec => []TypeOK /\ []NeighborInv /\ NoNewSource /\ Stabilization
=============================================================================