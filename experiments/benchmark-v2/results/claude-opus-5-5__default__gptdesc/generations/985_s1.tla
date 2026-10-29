------------------------------ MODULE YoYoAllGraphs ------------------------------
(***************************************************************************)
(* Yo-Yo leader election (without pruning) on arbitrary connected          *)
(* undirected graphs without self-loops. Nodes are integers; the node with *)
(* the smallest identifier is the eventual leader.                         *)
(* Each node keeps a local orientation of its edges (incoming / outgoing). *)
(* Initially edges are oriented from smaller to larger identifier.         *)
(* In the down phase, sources send their identifier to their outgoing      *)
(* neighbors. Other nodes wait for values from all incoming neighbors and  *)
(* forward the minimum. In the up phase, nodes wait for replies from all   *)
(* outgoing neighbors. They then reply "yes" to senders of the minimum and *)
(* "no" to everyone else. If any outgoing neighbor said "no", they reply   *)
(* "no" to all incoming neighbors. Edges carrying a "no" are reversed.     *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE Reach(_)
Reach(S) ==
  LET T == S \cup {m \in Nodes : \E k \in S : {m, k} \in Edges}
  IN  IF T = S THEN S ELSE Reach(T)

ASSUME
  /\ Nodes \subseteq Int
  /\ IsFiniteSet(Nodes)
  /\ Nodes # {}
  /\ Edges \subseteq SUBSET Nodes
  /\ \A e \in Edges : Cardinality(e) = 2          \* undirected, no self-loops
  /\ \A n \in Nodes : Reach({n}) = Nodes          \* (strongly) connected

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
MinNode == Min(Nodes)

Messages ==
     [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

kind(n) ==
  IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

(***************************************************************************)
(* Initial state: edges are oriented from smaller to larger identifier.    *)
(***************************************************************************)
Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase                                                               *)
(***************************************************************************)
DownSource(n) ==
  /\ kind(n) = "source"
  /\ phase[n] = "down"
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n]
                   THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> n]}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

DownOther(n) ==
  /\ kind(n) \in {"internal", "sink"}
  /\ phase[n] = "down"
  /\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
     IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
         /\ LET mn == Min({msg.val : msg \in downMsgs})
            IN  mailbox' = [m \in Nodes |->
                              IF m \in outgoing[n]
                              THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> mn]}
                              ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(***************************************************************************)
(* Up phase                                                                 *)
(***************************************************************************)
UpSource(n) ==
  /\ kind(n) = "source"
  /\ phase[n] = "up"
  /\ LET upMsgs   == {msg \in mailbox[n] : msg.phase = "up"}
         noSndrs  == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ upMsgs]
         /\ incoming' = [incoming EXCEPT ![n] = incoming[n] \cup noSndrs]
         /\ outgoing' = [outgoing EXCEPT ![n] = outgoing[n] \ noSndrs]
  /\ phase' = [phase EXCEPT ![n] = "down"]

UpOther(n) ==
  /\ kind(n) \in {"internal", "sink"}
  /\ phase[n] = "up"
  /\ LET upMsgs   == {msg \in mailbox[n] : msg.phase = "up"}
         downMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
         noSndrs  == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
         minSndrs == {msg.sndr : msg \in {mm \in downMsgs :
                                            \A mm2 \in downMsgs : mm.val <= mm2.val}}
         Yes(m)   == noSndrs = {} /\ m \in minSndrs
         noRcvrs  == {m \in incoming[n] : ~ Yes(m)}
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m \in incoming[n]
                          THEN mailbox[m] \cup
                                 {[phase |-> "up", sndr |-> n,
                                   reply |-> IF Yes(m) THEN "yes" ELSE "no"]}
                          ELSE IF m = n
                               THEN mailbox[n] \ (upMsgs \cup downMsgs)
                               ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] = (incoming[n] \ noRcvrs) \cup noSndrs]
         /\ outgoing' = [outgoing EXCEPT ![n] = (outgoing[n] \ noSndrs) \cup noRcvrs]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Node(n) == DownSource(n) \/ DownOther(n) \/ UpSource(n) \/ UpOther(n)

Next == \E n \in Nodes : Node(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Node(n))

(***************************************************************************)
(* Properties                                                               *)
(***************************************************************************)
TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

NeighborInv ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] = Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

\* No node that is not a source ever becomes a source.
NoNewSource ==
  [][\A n \in Nodes : kind(n)' = "source" => kind(n) = "source"]_vars

\* Stable state: the minimum node is the unique source, all up messages are "yes".
Stable ==
  /\ \A n \in Nodes : kind(n) = "source" <=> n = MinNode
  /\ \A n \in Nodes : \A msg \in mailbox[n] :
        msg.phase = "up" => msg.reply = "yes"

Stabilization == <>[]Stable

=============================================================================