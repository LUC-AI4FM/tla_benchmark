------------------------------- MODULE YoYoPruning -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Edges

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  LET T == S \cup {m \in Nodes : \E s \in S : {s, m} \in Edges}
  IN  IF T = S THEN S ELSE ReachFrom(T)

ASSUME
  /\ Nodes \subseteq Nat
  /\ Nodes # {}
  /\ Edges \subseteq {e \in SUBSET Nodes : Cardinality(e) = 2}
  /\ \A n \in Nodes : ReachFrom({n}) = Nodes

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinNode == Min(Nodes)

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

VARIABLES
  active,    \* has the node not (yet) been pruned?
  phase,     \* current phase of each node: "down" or "up"
  incoming,  \* incoming neighbors of each node
  outgoing,  \* outgoing neighbors of each node
  rcvd,      \* pairs <<sender, value>> received in the current down phase
  mailbox    \* messages in transit to each node

vars == <<active, phase, incoming, outgoing, rcvd, mailbox>>

kind(n) ==
  IF incoming[n] = {} /\ outgoing[n] = {} THEN "leader"
  ELSE IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

DownMessages == [phase : {"down"}, sndr : Nodes, val : Nodes]
UpMessages   == [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]
Messages == DownMessages \cup UpMessages

downMsg(s, v)    == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s, r, p)   == [phase |-> "up", sndr |-> s, reply |-> r, prune |-> p]

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ rcvd \in [Nodes -> SUBSET (Nodes \X Nodes)]
  /\ mailbox \in [Nodes -> SUBSET Messages]
  /\ \A n \in Nodes :
       /\ incoming[n] \subseteq Neighbors(n)
       /\ outgoing[n] \subseteq Neighbors(n)
       /\ incoming[n] \cap outgoing[n] = {}
       /\ ~active[n] => incoming[n] = {} /\ outgoing[n] = {}
       /\ kind(n) \in {"source", "internal", "sink", "leader"}
       /\ kind(n) = "source"   <=> incoming[n] = {} /\ outgoing[n] # {}
       /\ kind(n) = "sink"     <=> incoming[n] # {} /\ outgoing[n] = {}
       /\ kind(n) = "internal" <=> incoming[n] # {} /\ outgoing[n] # {}
       /\ kind(n) = "leader"   <=> incoming[n] = {} /\ outgoing[n] = {}
       \* at most one message per (phase, sender) in each mailbox
       /\ \A m1, m2 \in mailbox[n] :
            (m1.phase = m2.phase /\ m1.sndr = m2.sndr) => m1 = m2

\* Messages refer to currently adjacent nodes, except for down messages
\* sent across an edge whose reversal (a "no" reply) is still in flight.
NeighborInv ==
  \A n \in Nodes : \A msg \in mailbox[n] :
     /\ active[n]
     /\ msg.phase = "up" => msg.sndr \in outgoing[n]
     /\ msg.phase = "down" =>
          \/ msg.sndr \in incoming[n]
          \/ /\ msg.sndr \in outgoing[n]
             /\ \E u \in mailbox[n] :
                   /\ u.phase = "up"
                   /\ u.sndr = msg.sndr
                   /\ u.reply = "no"
                   /\ ~u.prune

Init ==
  /\ active = [n \in Nodes |-> TRUE]
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ rcvd = [n \in Nodes |-> {}]
  /\ mailbox = [n \in Nodes |-> {}]

-----------------------------------------------------------------------------
(* Down phase *)

DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ kind(n) = "source"
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, n)}
                   ELSE mailbox[m]]
  /\ rcvd' = [rcvd EXCEPT ![n] = {}]
  /\ UNCHANGED <<active, incoming, outgoing>>

DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ kind(n) \in {"internal", "sink"}
  /\ LET dm == {msg \in mailbox[n] : msg.phase = "down"}
     IN  /\ {msg.sndr : msg \in dm} = incoming[n]
         /\ LET mv == Min({msg.val : msg \in dm})
            IN  /\ phase' = [phase EXCEPT ![n] = "up"]
                /\ rcvd' = [rcvd EXCEPT ![n] = {<<msg.sndr, msg.val>> : msg \in dm}]
                /\ mailbox' = [m \in Nodes |->
                                 IF m = n THEN mailbox[n] \ dm
                                 ELSE IF m \in outgoing[n]
                                      THEN mailbox[m] \cup {downMsg(n, mv)}
                                      ELSE mailbox[m]]
  /\ UNCHANGED <<active, incoming, outgoing>>

-----------------------------------------------------------------------------
(* Up phase *)

UpSource(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ kind(n) = "source"
  /\ LET um    == {msg \in mailbox[n] : msg.phase = "up"}
         outNo == {msg.sndr : msg \in {x \in um : x.reply = "no" /\ ~x.prune}}
         outPr == {msg.sndr : msg \in {x \in um : x.prune}}
     IN  /\ {msg.sndr : msg \in um} = outgoing[n]
         /\ incoming' = [incoming EXCEPT ![n] = outNo]
         /\ outgoing' = [outgoing EXCEPT ![n] = outgoing[n] \ (outNo \cup outPr)]
         /\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ um]
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ rcvd' = [rcvd EXCEPT ![n] = {}]
  /\ UNCHANGED active

ValOf(n, s) == (CHOOSE p \in rcvd[n] : p[1] = s)[2]

UpOther(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ kind(n) \in {"internal", "sink"}
  /\ LET um     == {msg \in mailbox[n] : msg.phase = "up"}
         outNo  == {msg.sndr : msg \in {x \in um : x.reply = "no" /\ ~x.prune}}
         outPr  == {msg.sndr : msg \in {x \in um : x.prune}}
         vals   == {p[2] : p \in rcvd[n]}
         mv     == Min(vals)
         allYes == \A msg \in um : msg.reply = "yes"
         reply(s) == IF allYes /\ ValOf(n, s) = mv THEN "yes" ELSE "no"
     IN  /\ {msg.sndr : msg \in um} = outgoing[n]
         /\ \/ \* pruning rule (a): a sink with a single incoming neighbor
               /\ outgoing[n] = {}
               /\ Cardinality(incoming[n]) = 1
               /\ active' = [active EXCEPT ![n] = FALSE]
               /\ incoming' = [incoming EXCEPT ![n] = {}]
               /\ outgoing' = outgoing
               /\ mailbox' = [m \in Nodes |->
                                IF m = n THEN mailbox[n] \ um
                                ELSE IF m \in incoming[n]
                                     THEN mailbox[m] \cup {upMsg(n, "yes", TRUE)}
                                     ELSE mailbox[m]]
            \/ \* pruning rule (b): keep one incoming link per distinct value
               /\ ~(outgoing[n] = {} /\ Cardinality(incoming[n]) = 1)
               /\ \E keep \in [vals -> incoming[n]] :
                    /\ \A v \in vals : <<keep[v], v>> \in rcvd[n]
                    /\ LET kept   == {keep[v] : v \in vals}
                           pruned == incoming[n] \ kept
                           inNo   == {s \in kept : reply(s) = "no"}
                       IN  /\ incoming' = [incoming EXCEPT ![n] = (kept \ inNo) \cup outNo]
                           /\ outgoing' = [outgoing EXCEPT ![n] =
                                             (outgoing[n] \ (outNo \cup outPr)) \cup inNo]
                           /\ mailbox' = [m \in Nodes |->
                                            IF m = n THEN mailbox[n] \ um
                                            ELSE IF m \in incoming[n]
                                                 THEN mailbox[m] \cup
                                                        {upMsg(n, reply(m), m \in pruned)}
                                                 ELSE mailbox[m]]
               /\ UNCHANGED active
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ rcvd' = [rcvd EXCEPT ![n] = {}]

-----------------------------------------------------------------------------
Next == \E n \in Nodes :
          \/ DownSource(n)
          \/ DownOther(n)
          \/ UpSource(n)
          \/ UpOther(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Correctness properties *)

Finished ==
  /\ \A n \in Nodes \ {MinNode} : ~active[n]
  /\ active[MinNode]
  /\ kind(MinNode) = "leader"
  /\ \A n \in Nodes : mailbox[n] = {}

Leaders == {n \in Nodes : active[n] /\ kind(n) = "leader"}

AtMostOneLeader == Cardinality(Leaders) <= 1

LeaderIsMin == \A n \in Leaders : n = MinNode

FinishIffTerminated == (~ENABLED Next) <=> Finished

NoNewSource ==
  [][\A n \in Nodes : (active'[n] /\ kind(n)' = "source") => kind(n) = "source"]_vars

Liveness == <>Finished

=============================================================================