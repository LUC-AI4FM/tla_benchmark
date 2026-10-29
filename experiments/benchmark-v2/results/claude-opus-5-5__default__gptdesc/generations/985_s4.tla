---------------------------- MODULE YoYoNoPruning ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

(***************************************************************************)
(* Graph-related definitions                                              *)
(***************************************************************************)
Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

Reachable(n) ==
  LET R[k \in Nat] ==
        IF k = 0 THEN {n}
        ELSE R[k-1] \cup UNION {Neighbors(m) : m \in R[k-1]}
  IN  R[Cardinality(Nodes)]

IsUndirectedGraphNoSelfLoops ==
  Edges \subseteq {e \in SUBSET Nodes : Cardinality(e) = 2}

IsStronglyConnected ==
  \A m, n \in Nodes : m \in Reachable(n)

ASSUME
  /\ IsFiniteSet(Nodes)
  /\ Nodes # {}
  /\ Nodes \subseteq Int
  /\ IsUndirectedGraphNoSelfLoops
  /\ IsStronglyConnected

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

(***************************************************************************)
(* Variables                                                              *)
(***************************************************************************)
VARIABLES
  phase,     \* phase[n] \in {"down", "up"}
  incoming,  \* incoming[n] : neighbors with edges oriented towards n
  outgoing,  \* outgoing[n] : neighbors with edges oriented away from n
  mailbox    \* mailbox[n]  : set of messages received by n

vars == <<phase, incoming, outgoing, mailbox>>

kind(n) ==
  IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

Messages ==
       [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

down(n, v) == [phase |-> "down", sndr |-> n, val |-> v]
up(n, r)   == [phase |-> "up", sndr |-> n, reply |-> r]

(***************************************************************************)
(* Initial state: orient every edge from the smaller to the larger node.  *)
(***************************************************************************)
Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase                                                             *)
(***************************************************************************)
DownSource(n) ==
  /\ kind(n) = "source"
  /\ phase[n] = "down"
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n] THEN mailbox[m] \cup {down(n, n)}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

DownOther(n) ==
  /\ kind(n) # "source"
  /\ phase[n] = "down"
  /\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down"}
     IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
         /\ LET mn == Min({msg.val : msg \in downMsgs})
            IN  mailbox' = [m \in Nodes |->
                              IF m \in outgoing[n]
                              THEN mailbox[m] \cup {down(n, mn)}
                              ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

Down(n) == DownSource(n) \/ DownOther(n)

(***************************************************************************)
(* Up phase                                                               *)
(***************************************************************************)
UpSource(n) ==
  /\ kind(n) = "source"
  /\ phase[n] = "up"
  /\ LET upMsgs  == {msg \in mailbox[n] : msg.phase = "up"}
         noSndrs == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ mailbox' = [mailbox EXCEPT ![n] = {}]
         /\ incoming' = [incoming EXCEPT ![n] = noSndrs]
         /\ outgoing' = [outgoing EXCEPT ![n] = @ \ noSndrs]
  /\ phase' = [phase EXCEPT ![n] = "down"]

UpOther(n) ==
  /\ kind(n) # "source"
  /\ phase[n] = "up"
  /\ LET upMsgs   == {msg \in mailbox[n] : msg.phase = "up"}
         noSndrs  == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
         downMsgs == {msg \in mailbox[n] : msg.phase = "down"}
         mn       == Min({msg.val : msg \in downMsgs})
         minSndrs == {msg.sndr : msg \in {mm \in downMsgs : mm.val = mn}}
         yesRcvrs == IF noSndrs = {} THEN minSndrs ELSE {}
         noRcvrs  == incoming[n] \ yesRcvrs
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN {}
                          ELSE IF m \in yesRcvrs
                               THEN mailbox[m] \cup {up(n, "yes")}
                          ELSE IF m \in noRcvrs
                               THEN mailbox[m] \cup {up(n, "no")}
                          ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] = (@ \ noRcvrs) \cup noSndrs]
         /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noSndrs) \cup noRcvrs]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Up(n) == UpSource(n) \/ UpOther(n)

(***************************************************************************)
(* Next-state relation and specification                                  *)
(***************************************************************************)
Next == \E n \in Nodes : Down(n) \/ Up(n)

Fairness == \A n \in Nodes : WF_vars(Down(n) \/ Up(n))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                             *)
(***************************************************************************)
TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

NeighborConsistency ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] = Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

\* No node that is not a source becomes a source.
NoNewSource ==
  [][\A n \in Nodes : kind(n)' = "source" => kind(n) = "source"]_vars

AllUpYes ==
  \A n \in Nodes : \A msg \in mailbox[n] :
     msg.phase = "up" => msg.reply = "yes"

UniqueSourceIsMin ==
  \A n \in Nodes : kind(n) = "source" <=> n = MinNode

Stabilization == <>[](UniqueSourceIsMin /\ AllUpYes)

THEOREM Spec => [](TypeOK /\ NeighborConsistency)
THEOREM Spec => NoNewSource
THEOREM Spec => Stabilization
==============================================================================