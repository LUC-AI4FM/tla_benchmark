---------------------------- MODULE YoYoNoPruning ----------------------------
(***************************************************************************)
(* The Yo-Yo leader election algorithm for arbitrary undirected connected *)
(* graphs (N. Santoro, Design and Analysis of Distributed Algorithms),    *)
(* without the pruning optimization.                                       *)
(* Edges are initially oriented from smaller to larger identities.         *)
(* Sources (no incoming edges) are leader candidates and sinks have no     *)
(* outgoing edges. Each round has two phases:                              *)
(*   - down: sources send their identity along outgoing edges. Other nodes *)
(*     wait for values from all incoming neighbors and forward the minimum.*)
(*   - up: sinks answer "yes" to the neighbors that sent the minimum value *)
(*     and "no" to the others. Answers are propagated back towards the     *)
(*     sources. Edges along which "no" is sent are reversed.               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

ReachableFrom(n) ==
  LET R[i \in Nat] ==
        IF i = 0 THEN {n}
        ELSE R[i-1] \cup UNION {Neighbors(m) : m \in R[i-1]}
  IN  R[Cardinality(Nodes)]

ASSUME
  /\ IsFiniteSet(Nodes)
  /\ Nodes # {}
  /\ Nodes \subseteq Int
  /\ Edges \subseteq {{m, n} : m \in Nodes, n \in Nodes}
  /\ \A e \in Edges : Cardinality(e) = 2
  /\ \A n \in Nodes : ReachableFrom(n) = Nodes

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

downMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s, r)   == [phase |-> "up", sndr |-> s, reply |-> r]

Messages ==
       [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]
  /\ \A n \in Nodes : \A msg \in mailbox[n] : msg.sndr \in Neighbors(n)

(* Every neighbor is either an incoming or an outgoing neighbor, never both *)
NeighborInv ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] = Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

(* Down phase: sources send their own identity; other nodes wait for values
   from all incoming neighbors and forward the minimum value received. *)
Down(n) ==
  /\ phase[n] = "down"
  /\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
     IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
         /\ LET v == IF incoming[n] = {} THEN n
                     ELSE Min({msg.val : msg \in downMsgs})
            IN  mailbox' = [m \in Nodes |->
                              IF m \in outgoing[n]
                              THEN mailbox[m] \cup {downMsg(n, v)}
                              ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(* Up phase: wait for replies from all outgoing neighbors (none for sinks).
   If all replies are "yes", answer "yes" to incoming neighbors that sent
   the minimum value and "no" to the others; otherwise answer "no" to all
   incoming neighbors. Edges carrying "no" are reversed. *)
Up(n) ==
  /\ phase[n] = "up"
  /\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
         upMsgs   == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}
         minv     == IF incoming[n] = {} THEN n
                     ELSE Min({msg.val : msg \in downMsgs})
         noRcvd   == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
         yesTo    == IF noRcvd = {}
                     THEN {msg.sndr : msg \in {mm \in downMsgs : mm.val = minv}}
                     ELSE {}
         noTo     == incoming[n] \ yesTo
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ incoming' = [incoming EXCEPT ![n] = (@ \ noTo) \cup noRcvd]
         /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noRcvd) \cup noTo]
         /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ (downMsgs \cup upMsgs)
                          ELSE IF m \in yesTo THEN mailbox[m] \cup {upMsg(n, "yes")}
                          ELSE IF m \in noTo THEN mailbox[m] \cup {upMsg(n, "no")}
                          ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A n \in Nodes : WF_vars(Down(n)) /\ WF_vars(Up(n))

(* No new sources are ever created; sources can only be eliminated *)
NoNewSource ==
  [][\A n \in Nodes : incoming[n] # {} => incoming'[n] # {}]_vars

(* Eventually only the minimum node is a source, only the minimum identity
   is sent in the down phase, and all replies are "yes". *)
Liveness ==
  /\ <>[](\A n \in Nodes : incoming[n] = {} <=> n = MinNode)
  /\ <>[](\A n \in Nodes : \A msg \in mailbox[n] :
             msg.phase = "down" => msg.val = MinNode)
  /\ <>[](\A n \in Nodes : \A msg \in mailbox[n] :
             msg.phase = "up" => msg.reply = "yes")

THEOREM Spec => [](TypeOK /\ NeighborInv)
THEOREM Spec => NoNewSource
THEOREM Spec => Liveness
=============================================================================