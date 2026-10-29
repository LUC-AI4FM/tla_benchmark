------------------------------ MODULE MCYoYoNoPruning ------------------------------
(***************************************************************************)
(* Model-checking wrapper for the Yo-Yo leader election algorithm without  *)
(* pruning. The graph is fixed directly in this module. Without pruning    *)
(* the algorithm never terminates, so the liveness property below, "all    *)
(* nodes eventually remain in the down phase", is expected to be violated. *)
(* TLC reports such a violation as a counterexample trace.                 *)
(*                                                                         *)
(* The algorithm is included here so that the module is self-contained.   *)
(* It corresponds to                                                       *)
(*     INSTANCE YoYoNoPruning                                              *)
(* without substitutions.                                                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

(***************************************************************************)
(* Fixed small graph.                                                      *)
(***************************************************************************)
Nodes == {1, 2, 3, 4, 5}
Edges == {{1,2}, {2,3}, {3,4}, {4,1}, {2,5}}

(***************************************************************************)
(* Larger alternative graph (unused):                                      *)
(* Nodes == {2,3,4,5,6,7,8,9,10,11,12,13,14,15,16}                         *)
(* Edges == {{2,4},{2,6},{2,8},{3,4},{3,9},{4,12},{5,6},{5,10},{6,13},     *)
(*           {7,8},{7,11},{8,14},{9,15},{10,16},{11,16},{12,15},{13,14}}   *)
(***************************************************************************)

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES phase, incoming, outgoing, mailbox
vars == <<phase, incoming, outgoing, mailbox>>

Messages ==
    [phase : {"down"}, sndr : Nodes, val : Nodes, reply : {"none"}]
  \cup [phase : {"up"}, sndr : Nodes, val : {0}, reply : {"yes", "no"}]

DownMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v, reply |-> "none"]
UpMsg(s, r)   == [phase |-> "up",   sndr |-> s, val |-> 0, reply |-> r]

kind(n) ==
  IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

Init ==
  /\ phase    = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox  = [n \in Nodes |-> {}]

(* A source starts the down phase by sending its own id downstream. *)
DownSource(n) ==
  /\ phase[n] = "down"
  /\ kind(n) = "source"
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n] THEN mailbox[m] \cup {DownMsg(n, n)}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(* An internal node or sink waits for values from all incoming neighbors *)
(* and forwards the minimum downstream.                                  *)
DownOther(n) ==
  /\ phase[n] = "down"
  /\ kind(n) # "source"
  /\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down"}
     IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
         /\ LET mn == Min({msg.val : msg \in downMsgs})
            IN  mailbox' = [m \in Nodes |->
                              IF m \in outgoing[n]
                              THEN mailbox[m] \cup {DownMsg(n, mn)}
                              ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(* An internal node or sink, having received replies from all outgoing   *)
(* neighbors, replies to its incoming neighbors and reverses edges.      *)
UpOther(n) ==
  /\ phase[n] = "up"
  /\ kind(n) # "source"
  /\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down"}
         upMsgs   == {msg \in mailbox[n] : msg.phase = "up"}
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ {msg.sndr : msg \in downMsgs} = incoming[n]
         /\ LET mn      == Min({msg.val : msg \in downMsgs})
                allYes  == \A msg \in upMsgs : msg.reply = "yes"
                yesTo   == IF allYes
                           THEN {msg.sndr : msg \in {d \in downMsgs : d.val = mn}}
                           ELSE {}
                noTo    == incoming[n] \ yesTo
                noFrom  == {msg.sndr : msg \in {u \in upMsgs : u.reply = "no"}}
            IN  /\ mailbox' = [m \in Nodes |->
                                 IF m = n THEN mailbox[n] \ (downMsgs \cup upMsgs)
                                 ELSE IF m \in yesTo THEN mailbox[m] \cup {UpMsg(n, "yes")}
                                 ELSE IF m \in noTo  THEN mailbox[m] \cup {UpMsg(n, "no")}
                                 ELSE mailbox[m]]
                /\ incoming' = [incoming EXCEPT ![n] = (@ \ noTo) \cup noFrom]
                /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noFrom) \cup noTo]
  /\ phase' = [phase EXCEPT ![n] = "down"]

(* A source, having received replies from all outgoing neighbors,        *)
(* reverses edges for which it received "no" and starts a new round.     *)
UpSource(n) ==
  /\ phase[n] = "up"
  /\ kind(n) = "source"
  /\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up"}
         noFrom == {msg.sndr : msg \in {u \in upMsgs : u.reply = "no"}}
     IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
         /\ mailbox'  = [mailbox EXCEPT ![n] = @ \ upMsgs]
         /\ incoming' = [incoming EXCEPT ![n] = @ \cup noFrom]
         /\ outgoing' = [outgoing EXCEPT ![n] = @ \ noFrom]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next ==
  \E n \in Nodes : DownSource(n) \/ DownOther(n) \/ UpOther(n) \/ UpSource(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
  /\ phase    \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox  \in [Nodes -> SUBSET Messages]

NeighborInv ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] = Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

NoNewSource ==
  [][\A n \in Nodes : kind(n)' = "source" => kind(n) = "source"]_vars

(* Eventually all nodes remain permanently in the down phase.            *)
(* Without pruning this property is violated; TLC produces a             *)
(* counterexample (recorded as PostCondition in the original file).      *)
Liveness == <>[](\A n \in Nodes : phase[n] = "down")

=============================================================================