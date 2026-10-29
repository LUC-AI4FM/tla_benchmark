--------------------------- MODULE YoYoNoPruning ---------------------------
(***************************************************************************)
(* Yo-Yo leader election on an arbitrary undirected, connected graph      *)
(* without self-loops, modeled WITHOUT graph pruning. Nodes run rounds    *)
(* forever. Each round has a "down" phase and an "up" phase. The system   *)
(* stabilizes when the node with the smallest identity is the only source *)
(* (candidate).                                                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  LET T == S \cup UNION {Neighbors(x) : x \in S}
  IN  IF T = S THEN S ELSE ReachFrom(T)

ASSUME
  /\ Nodes \subseteq Int
  /\ Nodes # {}
  /\ IsFiniteSet(Nodes)
  /\ \A e \in Edges : \E m, n \in Nodes : m # n /\ e = {m, n}   \* undirected, no self-loops
  /\ \A n \in Nodes : ReachFrom({n}) = Nodes                      \* connected

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

VARIABLES
  phase,     \* phase[n] \in {"down", "up"}
  incoming,  \* incoming[n]: neighbors oriented towards n (as seen by n)
  outgoing,  \* outgoing[n]: neighbors oriented away from n (as seen by n)
  mailbox    \* mailbox[n]: set of messages pending at n

vars == <<phase, incoming, outgoing, mailbox>>

DownMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
UpMsg(s, r)   == [phase |-> "up", sndr |-> s, reply |-> r]

Messages ==
       [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

IsSource(n) == incoming[n] = {}
Sources     == {n \in Nodes : IsSource(n)}

(***************************************************************************)
(* Type correctness                                                        *)
(***************************************************************************)
TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]
  /\ \A n \in Nodes :
       /\ incoming[n] \cup outgoing[n] = Neighbors(n)
       /\ incoming[n] \cap outgoing[n] = {}
       /\ \A msg \in mailbox[n] : msg.sndr \in Neighbors(n)

(***************************************************************************)
(* Initial state: edges oriented from smaller to larger identity.          *)
(***************************************************************************)
Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase: once a node has received values from all incoming          *)
(* neighbors (immediately, for a source), it forwards the minimum value   *)
(* (its own identity, for a source) to all outgoing neighbors.            *)
(***************************************************************************)
Down(n) ==
  /\ phase[n] = "down"
  /\ LET downMsgs == {msg \in mailbox[n] :
                        msg.phase = "down" /\ msg.sndr \in incoming[n]}
     IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
         /\ LET v == IF incoming[n] = {} THEN n
                     ELSE Min({msg.val : msg \in downMsgs})
            IN  mailbox' = [m \in Nodes |->
                              IF m \in outgoing[n]
                              THEN mailbox[m] \cup {DownMsg(n, v)}
                              ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(***************************************************************************)
(* Up phase: once a node has received replies from all outgoing neighbors *)
(* (immediately, for a sink), it replies "yes" to the incoming neighbors  *)
(* that sent the minimum value, provided all replies it received were     *)
(* "yes"; otherwise "no". Edges carrying "no" are reversed.               *)
(***************************************************************************)
Up(n) ==
  /\ phase[n] = "up"
  /\ LET upMsgs   == {msg \in mailbox[n] :
                        msg.phase = "up" /\ msg.sndr \in outgoing[n]}
         downMsgs == {msg \in mailbox[n] :
                        msg.phase = "down" /\ msg.sndr \in incoming[n]}
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ LET noSndrs  == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
                minVal   == IF downMsgs = {} THEN n
                            ELSE Min({msg.val : msg \in downMsgs})
                yesRcvrs == IF noSndrs = {}
                            THEN {msg.sndr : msg \in {mm \in downMsgs : mm.val = minVal}}
                            ELSE {}
                noRcvrs  == incoming[n] \ yesRcvrs
            IN  /\ mailbox' = [m \in Nodes |->
                                 IF m = n THEN mailbox[n] \ (upMsgs \cup downMsgs)
                                 ELSE IF m \in yesRcvrs
                                      THEN mailbox[m] \cup {UpMsg(n, "yes")}
                                 ELSE IF m \in noRcvrs
                                      THEN mailbox[m] \cup {UpMsg(n, "no")}
                                 ELSE mailbox[m]]
                /\ incoming' = [incoming EXCEPT ![n] = (@ \ noRcvrs) \cup noSndrs]
                /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noSndrs) \cup noRcvrs]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Step(n) == Down(n) \/ Up(n)

Next == \E n \in Nodes : Step(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Step(n))

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
\* Edge orientation is consistent between neighbors, except while a "no"
\* reply that reverses the edge is still in transit.
EdgeOK ==
  \A m, n \in Nodes : {m, n} \in Edges =>
    \/ m \in outgoing[n] /\ n \in incoming[m]
    \/ m \in incoming[n] /\ n \in outgoing[m]
    \/ /\ m \in outgoing[n] /\ n \in outgoing[m]
       /\ \/ UpMsg(m, "no") \in mailbox[n]
          \/ UpMsg(n, "no") \in mailbox[m]

\* No new candidates are ever created.
NoNewSource ==
  [][\A n \in Nodes : IsSource(n)' => IsSource(n)]_vars

\* The minimum node always remains a candidate.
MinNodeIsSource == IsSource(MinNode)

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
Stable ==
  /\ Sources = {MinNode}
  /\ \A n \in Nodes : \A msg \in mailbox[n] :
       /\ msg.phase = "down" => msg.val = MinNode
       /\ msg.phase = "up"   => msg.reply = "yes"

Stabilization == <>[]Stable

\* Multiple candidates cannot persist indefinitely.
MultipleSourcesReduce ==
  (Cardinality(Sources) > 1) ~> (Cardinality(Sources) = 1)

THEOREM Spec => [](TypeOK /\ EdgeOK /\ MinNodeIsSource)
THEOREM Spec => NoNewSource
THEOREM Spec => Stabilization /\ MultipleSourcesReduce
=============================================================================