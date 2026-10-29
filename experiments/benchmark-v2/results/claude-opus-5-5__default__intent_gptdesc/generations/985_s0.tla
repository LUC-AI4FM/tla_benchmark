------------------------------ MODULE YoYoNoPruning ------------------------------
(***************************************************************************)
(* The Yo-Yo leader election algorithm on an arbitrary undirected,         *)
(* connected graph whose nodes carry distinct integer identifiers.         *)
(*                                                                         *)
(* Each round has two phases:                                              *)
(*  - "down": sources broadcast their identity along outgoing edges.       *)
(*    Every other node waits for values from all incoming neighbors, then  *)
(*    forwards the minimum it received to all outgoing neighbors. Sinks    *)
(*    send nothing in this phase.                                          *)
(*  - "up": sinks reply "yes" to the incoming neighbors that sent the      *)
(*    minimum and "no" to the others. Internal nodes wait for replies from *)
(*    all outgoing neighbors. If any reply is "no", they send "no" to all  *)
(*    incoming neighbors. Otherwise they reply "yes" only to the incoming  *)
(*    neighbors that sent the minimum and "no" to the others. Sources wait *)
(*    for the replies and send nothing.                                    *)
(* Every edge along which "no" is sent is reversed. The sender of "no"     *)
(* flips the edge immediately. The receiver flips it when it processes     *)
(* the "no" message. Pending "no" messages therefore record reversals that *)
(* are still in flight.                                                    *)
(*                                                                         *)
(* This model contains no pruning and no termination detection. It is      *)
(* organised so that a pruning variant can refine the Up step. That        *)
(* variant would extend the variables and strengthen UpStep.               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

Connected ==
  \A S \in SUBSET Nodes :
     (S # {} /\ S # Nodes) => \E e \in Edges : e \cap S # {} /\ e \ S # {}

ASSUME
  /\ Nodes \subseteq Int
  /\ IsFiniteSet(Nodes)
  /\ Nodes # {}
  /\ Edges \subseteq {e \in SUBSET Nodes : Cardinality(e) = 2}
  /\ Connected

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinId == Min(Nodes)

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

(* Message constructors *)
DownMsg(s, v) == [type |-> "down", sndr |-> s, val |-> v]
UpMsg(s, r)   == [type |-> "up", sndr |-> s, reply |-> r]

Messages ==
     [type : {"down"}, sndr : Nodes, val : Nodes]
  \cup [type : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

VARIABLES
  phase,      \* phase[n] \in {"down", "up"}
  incoming,   \* incoming[n] : neighbors n currently considers oriented towards n
  outgoing,   \* outgoing[n] : neighbors n currently considers oriented away from n
  mailbox,    \* mailbox[n]  : set of messages in flight to n
  downRcvd    \* downRcvd[n] : down messages consumed by n in the current round

vars == <<phase, incoming, outgoing, mailbox, downRcvd>>

kind(n) ==
  IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

Sources == {n \in Nodes : incoming[n] = {}}

DownMsgs(n) == {msg \in mailbox[n] : msg.type = "down"}
UpMsgs(n)   == {msg \in mailbox[n] : msg.type = "up"}

TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]
  /\ downRcvd \in [Nodes -> SUBSET Messages]

-----------------------------------------------------------------------------
Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]
  /\ downRcvd = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase. A source has no incoming neighbors, so it proceeds          *)
(* immediately and sends its own identity. Any other node waits until it   *)
(* has a down message from every incoming neighbor, then forwards the      *)
(* minimum value. A sink has no outgoing neighbors, so it sends nothing.   *)
(***************************************************************************)
DownStep(n) ==
  /\ phase[n] = "down"
  /\ LET D   == DownMsgs(n)
         val == IF kind(n) = "source" THEN n ELSE Min({d.val : d \in D})
     IN  /\ {d.sndr : d \in D} = incoming[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ D
                          ELSE IF m \in outgoing[n]
                               THEN mailbox[m] \cup {DownMsg(n, val)}
                               ELSE mailbox[m]]
         /\ downRcvd' = [downRcvd EXCEPT ![n] = D]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

(***************************************************************************)
(* Up phase. Node n waits for replies from all outgoing neighbors. A sink  *)
(* has none, so it proceeds at once. The rules for which neighbors get     *)
(* "yes" and which get "no" are given in the module header. Every edge     *)
(* along which n sends "no" is reversed in n's view immediately. Every     *)
(* edge along which n received "no" is reversed in n's view now, when n    *)
(* consumes the reply.                                                     *)
(***************************************************************************)
UpStep(n) ==
  /\ phase[n] = "up"
  /\ LET U      == UpMsgs(n)
         D      == downRcvd[n]
         minV   == IF D = {} THEN n ELSE Min({d.val : d \in D})
         minS   == {d.sndr : d \in {e \in D : e.val = minV}}
         noFrom == {u.sndr : u \in {v \in U : v.reply = "no"}}
         noTo   == IF noFrom = {} THEN incoming[n] \ minS ELSE incoming[n]
         yesTo  == incoming[n] \ noTo
     IN  /\ {u.sndr : u \in U} = outgoing[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ U
                          ELSE IF m \in noTo
                               THEN mailbox[m] \cup {UpMsg(n, "no")}
                          ELSE IF m \in yesTo
                               THEN mailbox[m] \cup {UpMsg(n, "yes")}
                          ELSE mailbox[m]]
         /\ incoming' = [incoming EXCEPT ![n] = (incoming[n] \ noTo) \cup noFrom]
         /\ outgoing' = [outgoing EXCEPT ![n] = (outgoing[n] \ noFrom) \cup noTo]
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ downRcvd' = [downRcvd EXCEPT ![n] = {}]

Next == \E n \in Nodes : DownStep(n) \/ UpStep(n)

Fairness == \A n \in Nodes : WF_vars(DownStep(n) \/ UpStep(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* Every neighbor is either incoming or outgoing, never both. *)
OrientationInv ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] = Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

(***************************************************************************)
(* Neighbor/message consistency during reversals. The views of n and m on  *)
(* their edge agree unless m has sent a "no" to n that n has not processed *)
(* yet. In that case m has already reversed the edge and n has not.        *)
(***************************************************************************)
NeighborInv ==
  \A n \in Nodes : \A m \in Neighbors(n) :
     m \in outgoing[n] <=>
        \/ /\ n \in incoming[m]
           /\ UpMsg(m, "no") \notin mailbox[n]
        \/ /\ n \in outgoing[m]
           /\ UpMsg(m, "no") \in mailbox[n]

(* No new sources are ever created; reversals only remove sources. *)
NoNewSources ==
  [][\A n \in Nodes : incoming[n] # {} => incoming'[n] # {}]_vars

(* The node with the smallest identifier always remains a source. *)
MinIsSource == MinId \in Sources

Inv == TypeOK /\ OrientationInv /\ NeighborInv /\ MinIsSource

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Eventually the node with the minimal identifier is the unique source. *)
EventuallyUniqueSource == <>[](Sources = {MinId})

(***************************************************************************)
(* Stabilization: there is exactly one source, MinId. Every down message   *)
(* in flight carries MinId, and every up reply in flight is "yes".         *)
(***************************************************************************)
Stable ==
  /\ Sources = {MinId}
  /\ \A n \in Nodes : \A msg \in mailbox[n] :
        /\ msg.type = "down" => msg.val = MinId
        /\ msg.type = "up"   => msg.reply = "yes"

Stabilization == <>[]Stable

THEOREM Spec => []Inv
THEOREM Spec => NoNewSources
THEOREM Spec => EventuallyUniqueSource /\ Stabilization
=============================================================================