------------------------------- MODULE YoYoAllGraphs -------------------------------
(***************************************************************************)
(* Yo-Yo leader election on arbitrary connected undirected graphs without  *)
(* self-loops. Nodes are integers; the node with the smallest identifier   *)
(* becomes the leader. Edges are oriented through the sets incoming[n] and *)
(* outgoing[n]. Each node alternates between a down phase, which propagates *)
(* minimum identifiers towards sinks, and an up phase, which sends yes/no   *)
(* replies back towards sources. Edges on which "no" is sent are reversed.  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

ASSUME /\ Nodes \subseteq Int
       /\ IsFiniteSet(Nodes)
       /\ Nodes # {}
       /\ Edges \subseteq SUBSET Nodes
       /\ \A e \in Edges : Cardinality(e) = 2   \* undirected, no self-loops

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

ReachableFrom(n) ==
  LET R[k \in Nat] ==
        IF k = 0 THEN {n}
        ELSE R[k-1] \cup {y \in Nodes : \E x \in R[k-1] : {x, y} \in Edges}
  IN  R[Cardinality(Nodes)]

\* the input graph is (strongly) connected
ASSUME \A n \in Nodes : ReachableFrom(n) = Nodes

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

Messages ==
       [type : {"down"}, sndr : Nodes, val : Nodes]
  \cup [type : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase: a source sends its own identifier along outgoing edges; any *)
(* other node waits for values from all incoming neighbors and forwards    *)
(* the minimum of these values along its outgoing edges.                   *)
(***************************************************************************)
Down(n) ==
  /\ phase[n] = "down"
  /\ \A m \in incoming[n] :
        \E msg \in mailbox[n] : msg.type = "down" /\ msg.sndr = m
  /\ LET downs == {x \in mailbox[n] : x.type = "down" /\ x.sndr \in incoming[n]}
         v     == IF incoming[n] = {} THEN n ELSE Min({x.val : x \in downs})
     IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n]
                       THEN mailbox[m] \cup {[type |-> "down", sndr |-> n, val |-> v]}
                       ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(***************************************************************************)
(* Up phase: a node waits for replies from all outgoing neighbors. If some *)
(* reply is "no", it replies "no" to all incoming neighbors; otherwise it  *)
(* replies "yes" to those incoming neighbors that sent the minimum value   *)
(* and "no" to the others. Edges carrying a "no" are reversed.             *)
(***************************************************************************)
Up(n) ==
  /\ phase[n] = "up"
  /\ \A m \in outgoing[n] :
        \E msg \in mailbox[n] : msg.type = "up" /\ msg.sndr = m
  /\ LET downs  == {x \in mailbox[n] : x.type = "down" /\ x.sndr \in incoming[n]}
         ups    == {x \in mailbox[n] : x.type = "up" /\ x.sndr \in outgoing[n]}
         noSnd  == {x.sndr : x \in {u \in ups : u.reply = "no"}}
         minVal == IF downs = {} THEN n ELSE Min({x.val : x \in downs})
         yesTo  == IF noSnd = {}
                   THEN {x.sndr : x \in {d \in downs : d.val = minVal}}
                   ELSE {}
         noTo   == incoming[n] \ yesTo
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ (downs \cup ups)
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup
                                      {[type |-> "up", sndr |-> n,
                                        reply |-> IF m \in yesTo THEN "yes" ELSE "no"]}
                               ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] = (@ \ noTo) \cup noSnd]
         /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noSnd) \cup noTo]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(Down(n) \/ Up(n))

---------------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

NeighborConsistency ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] = Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

MinNodeIsSource == incoming[MinNode] = {}

\* no node that is not a source ever becomes a source
NoNewSources ==
  [][\A n \in Nodes : incoming[n] # {} => incoming'[n] # {}]_vars

---------------------------------------------------------------------------------
(* Liveness: eventually the minimum node is the unique source, and all     *)
(* up messages are "yes".                                                  *)

Stabilized ==
  /\ \A n \in Nodes : (incoming[n] = {}) <=> (n = MinNode)
  /\ \A n \in Nodes : \A msg \in mailbox[n] :
        msg.type = "up" => msg.reply = "yes"

Liveness == <>[]Stabilized

THEOREM Spec => [](TypeOK /\ NeighborConsistency /\ MinNodeIsSource)
THEOREM Spec => NoNewSources
THEOREM Spec => Liveness
=================================================================================