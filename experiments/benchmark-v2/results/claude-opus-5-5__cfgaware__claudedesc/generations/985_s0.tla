------------------------------- MODULE YoYoNoPruning -------------------------------
EXTENDS TLC, Integers, FiniteSets

CONSTANTS Nodes, Edges

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

ReachableFrom(n) ==
  LET R[k \in Nat] ==
        IF k = 0 THEN {n}
        ELSE R[k-1] \cup {y \in Nodes : \E x \in R[k-1] : {x, y} \in Edges}
  IN  R[Cardinality(Nodes)]

ASSUME
  /\ Nodes \subseteq Int
  /\ IsFiniteSet(Nodes)
  /\ Edges \subseteq {{m, n} : m, n \in Nodes}
  /\ \A e \in Edges : Cardinality(e) = 2
  /\ \A n \in Nodes : ReachableFrom(n) = Nodes

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES
  phase,
  incoming,
  outgoing,
  mailbox

vars == <<phase, incoming, outgoing, mailbox>>

Messages ==
  [phase : {"down"}, sndr : Nodes, val : Nodes] \cup
  [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

downMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s, r)   == [phase |-> "up", sndr |-> s, reply |-> r]

kind(n) ==
  IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ \A n \in Nodes : incoming[n] \subseteq Neighbors(n)
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ \A n \in Nodes : outgoing[n] \subseteq Neighbors(n)
  /\ mailbox \in [Nodes -> SUBSET Messages]

Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

(* Down phase of a source: broadcast its own identity. *)
DownSource(n) ==
  /\ kind(n) = "source"
  /\ phase[n] = "down"
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, n)}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(* Down phase of a non-source: wait for all incoming values, forward the minimum. *)
DownOther(n) ==
  /\ kind(n) # "source"
  /\ phase[n] = "down"
  /\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down"}
     IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
         /\ LET min == Min({msg.val : msg \in downMsgs})
            IN  mailbox' = [m \in Nodes |->
                              IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, min)}
                              ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

Down(n) == DownSource(n) \/ DownOther(n)

(* Up phase of a source: collect replies, reverse edges on which "no" was received. *)
UpSource(n) ==
  /\ kind(n) = "source"
  /\ phase[n] = "up"
  /\ LET upMsgs  == {msg \in mailbox[n] : msg.phase = "up"}
         noSndrs == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ upMsgs]
         /\ incoming' = [incoming EXCEPT ![n] = noSndrs]
         /\ outgoing' = [outgoing EXCEPT ![n] = outgoing[n] \ noSndrs]
  /\ phase' = [phase EXCEPT ![n] = "down"]

(* Up phase of a non-source: once all replies from outgoing neighbors are in,
   respond to incoming neighbors and reverse edges accordingly. *)
UpOther(n) ==
  /\ kind(n) # "source"
  /\ phase[n] = "up"
  /\ LET upMsgs   == {msg \in mailbox[n] : msg.phase = "up"}
         noSndrs  == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
         downMsgs == {msg \in mailbox[n] : msg.phase = "down"}
         min      == Min({msg.val : msg \in downMsgs})
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ IF noSndrs = {}
            THEN LET yesIn == {msg.sndr : msg \in {mm \in downMsgs : mm.val = min}}
                     noIn  == {msg.sndr : msg \in {mm \in downMsgs : mm.val # min}}
                 IN  /\ mailbox' = [m \in Nodes |->
                                      IF m = n THEN mailbox[m] \ (upMsgs \cup downMsgs)
                                      ELSE IF m \in yesIn THEN mailbox[m] \cup {upMsg(n, "yes")}
                                      ELSE IF m \in noIn THEN mailbox[m] \cup {upMsg(n, "no")}
                                      ELSE mailbox[m]]
                     /\ incoming' = [incoming EXCEPT ![n] = incoming[n] \ noIn]
                     /\ outgoing' = [outgoing EXCEPT ![n] = outgoing[n] \cup noIn]
            ELSE /\ mailbox' = [m \in Nodes |->
                                  IF m = n THEN mailbox[m] \ (upMsgs \cup downMsgs)
                                  ELSE IF m \in incoming[n] THEN mailbox[m] \cup {upMsg(n, "no")}
                                  ELSE mailbox[m]]
                 /\ incoming' = [incoming EXCEPT ![n] = noSndrs]
                 /\ outgoing' = [outgoing EXCEPT ![n] = incoming[n] \cup (outgoing[n] \ noSndrs)]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Up(n) == UpSource(n) \/ UpOther(n)

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A n \in Nodes : WF_vars(Down(n)) /\ WF_vars(Up(n))

-----------------------------------------------------------------------------------
(* Properties *)

(* Every neighbor is either incoming or outgoing, but never both. *)
NeighborInv ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] = Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

(* Sources are never created, only eliminated. *)
NoNewSource ==
  [][\A n \in Nodes : kind(n)' = "source" => kind(n) = "source"]_vars

(* Eventually only the minimum node is a source, only the minimum identity
   is sent downwards, and all replies are "yes". *)
Liveness ==
  /\ <>[](/\ kind(Min(Nodes)) = "source"
          /\ \A n \in Nodes \ {Min(Nodes)} : kind(n) # "source")
  /\ <>[](\A n \in Nodes : \A msg \in mailbox[n] :
             msg.phase = "down" => msg.val = Min(Nodes))
  /\ <>[](\A n \in Nodes : \A msg \in mailbox[n] :
             msg.phase = "up" => msg.reply = "yes")

===================================================================================