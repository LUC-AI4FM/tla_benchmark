------------------------------ MODULE YoYoPruning ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Edges

ASSUME Edges \subseteq SUBSET Nodes

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Neighbors(n) == {m \in Nodes \ {n} : {m, n} \in Edges}

VARIABLES active, phase, incoming, outgoing, mailbox

vars == <<active, phase, incoming, outgoing, mailbox>>

Messages ==
    [type : {"down"}, sndr : Nodes, val : Nodes]
  \cup [type : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]

kind(n) ==
    IF incoming[n] = {} THEN "source"
    ELSE IF outgoing[n] = {} THEN "sink"
    ELSE "internal"

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

Init ==
  /\ active = [n \in Nodes |-> TRUE]
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

DownMsgs(n) ==
  {msg \in mailbox[n] : msg.type = "down" /\ msg.sndr \in incoming[n]}

UpMsgs(n) ==
  {msg \in mailbox[n] : msg.type = "up"}

SendDown(n, v) ==
  mailbox' = [m \in Nodes |->
                IF m \in outgoing[n]
                THEN mailbox[m] \cup {[type |-> "down", sndr |-> n, val |-> v]}
                ELSE mailbox[m]]

(* A source starts the down phase by sending its own identity *)
DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] = {}
  /\ outgoing[n] # {}
  /\ SendDown(n, n)
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* An internal node or sink forwards the minimum received value *)
DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ \A m \in incoming[n] :
        \E msg \in mailbox[n] : msg.type = "down" /\ msg.sndr = m
  /\ LET v == Min({msg.val : msg \in DownMsgs(n)})
     IN  SendDown(n, v)
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* Up phase: once replies from all out-neighbors are received, reply to
   in-neighbors, prune, and flip edges *)
Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ \A m \in outgoing[n] :
        \E msg \in mailbox[n] : msg.type = "up" /\ msg.sndr = m
  /\ LET upMsgs   == UpMsgs(n)
         downMsgs == DownMsgs(n)
         noRcvd   == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
         prunedOut == {msg.sndr : msg \in {mm \in upMsgs : mm.prune}}
         flipOut  == noRcvd \ prunedOut
         valOf(m) == (CHOOSE msg \in downMsgs : msg.sndr = m).val
         mn       == Min({msg.val : msg \in downMsgs})
         keep(v)  == CHOOSE m \in incoming[n] : valOf(m) = v
         pruneSelf == outgoing[n] = {} /\ Cardinality(incoming[n]) = 1
         replyTo(m) == IF noRcvd # {} THEN "no"
                       ELSE IF valOf(m) = mn THEN "yes" ELSE "no"
         prunedIn == IF pruneSelf THEN incoming[n]
                     ELSE {m \in incoming[n] : m # keep(valOf(m))}
         flipIn   == {m \in incoming[n] \ prunedIn : replyTo(m) = "no"}
     IN  /\ active' = [active EXCEPT ![n] = ~pruneSelf]
         /\ incoming' = [incoming EXCEPT ![n] =
                IF pruneSelf THEN {}
                ELSE (incoming[n] \ (prunedIn \cup flipIn)) \cup flipOut]
         /\ outgoing' = [outgoing EXCEPT ![n] =
                IF pruneSelf THEN {}
                ELSE (outgoing[n] \ (prunedOut \cup flipOut)) \cup flipIn]
         /\ phase' = [phase EXCEPT ![n] = "down"]
         /\ mailbox' = [m \in Nodes |->
                IF m = n THEN mailbox[n] \ (upMsgs \cup downMsgs)
                ELSE IF m \in incoming[n]
                     THEN mailbox[m] \cup
                            {[type |-> "up", sndr |-> n,
                              reply |-> replyTo(m), prune |-> m \in prunedIn]}
                     ELSE mailbox[m]]

Step == \E n \in Nodes : DownSource(n) \/ DownOther(n) \/ Up(n)

Finished ==
  \A n \in Nodes :
     IF n = Min(Nodes)
     THEN /\ active[n]
          /\ phase[n] = "down"
          /\ incoming[n] = {}
          /\ outgoing[n] = {}
     ELSE ~active[n]

Terminating == Finished /\ UNCHANGED vars

Next == Step \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Properties *)

NeighborInv ==
  /\ \A n \in Nodes :
       /\ incoming[n] \subseteq Neighbors(n)
       /\ outgoing[n] \subseteq Neighbors(n)
       /\ incoming[n] \cap outgoing[n] = {}
       /\ n \notin incoming[n] \cup outgoing[n]
  /\ \A m, n \in Nodes :
       (active[m] /\ active[n] /\ phase[m] = "down" /\ phase[n] = "down")
         => (m \in outgoing[n] <=> n \in incoming[m])

MinNeverPruned == active[Min(Nodes)]

FinishIffTerminated == Finished <=> ~ENABLED Step

Liveness == <>[]Finished

=============================================================================