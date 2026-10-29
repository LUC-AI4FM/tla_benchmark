---------------------------- MODULE MCYoYoPruning ----------------------------
EXTENDS Naturals, FiniteSets

Nodes == {1, 2, 3, 4, 5}
Edges == {{1,2}, {1,3}, {2,3}, {2,4}, {3,5}, {4,5}}

VARIABLES active, phase, incoming, outgoing, mailbox

vars == <<active, phase, incoming, outgoing, mailbox>>

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Messages ==
  [type : {"down", "up"}, sndr : Nodes, val : Nodes \cup {0},
   reply : {"yes", "no", "none"}, prune : BOOLEAN]

DownMsg(n, v) ==
  [type |-> "down", sndr |-> n, val |-> v, reply |-> "none", prune |-> FALSE]

UpMsg(n, r, p) ==
  [type |-> "up", sndr |-> n, val |-> 0, reply |-> r, prune |-> p]

DownMsgs(n) == {msg \in mailbox[n] : msg.type = "down" /\ msg.sndr \in incoming[n]}
UpMsgs(n)   == {msg \in mailbox[n] : msg.type = "up"}

Init ==
  /\ active   = [n \in Nodes |-> TRUE]
  /\ phase    = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox  = [n \in Nodes |-> {}]

DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] = {}
  /\ outgoing[n] # {}
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ mailbox' = [k \in Nodes |->
                   IF k \in outgoing[n]
                   THEN mailbox[k] \cup {DownMsg(n, n)}
                   ELSE mailbox[k]]
  /\ UNCHANGED <<active, incoming, outgoing>>

DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ {msg.sndr : msg \in DownMsgs(n)} = incoming[n]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ LET mn == Min({msg.val : msg \in DownMsgs(n)})
     IN  mailbox' = [k \in Nodes |->
                       IF k \in outgoing[n]
                       THEN mailbox[k] \cup {DownMsg(n, mn)}
                       ELSE mailbox[k]]
  /\ UNCHANGED <<active, incoming, outgoing>>

Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] \cup outgoing[n] # {}
  /\ {msg.sndr : msg \in UpMsgs(n)} = outgoing[n]
  /\ LET dm == DownMsgs(n)
         um == UpMsgs(n)
         ValOf(m)  == (CHOOSE msg \in dm : msg.sndr = m).val
         RecvOf(o) == CHOOSE msg \in um : msg.sndr = o
         vals == {msg.val : msg \in dm}
         mn == IF vals = {} THEN 0 ELSE Min(vals)
         noOut == \E msg \in um : msg.reply = "no"
         isSink == outgoing[n] = {}
         selfPrune == isSink /\ Cardinality(vals) = 1
         Keeper(v) == Min({m \in incoming[n] : ValOf(m) = v})
         Reply(m) == IF noOut THEN "no"
                     ELSE IF ValOf(m) = mn THEN "yes" ELSE "no"
         Prune(m) == selfPrune \/ m # Keeper(ValOf(m))
         newIn  == {m \in incoming[n] : Reply(m) = "yes" /\ ~Prune(m)}
                   \cup {o \in outgoing[n] : RecvOf(o).reply = "no" /\ ~RecvOf(o).prune}
         newOut == {m \in incoming[n] : Reply(m) = "no" /\ ~Prune(m)}
                   \cup {o \in outgoing[n] : RecvOf(o).reply = "yes" /\ ~RecvOf(o).prune}
     IN  /\ mailbox' = [k \in Nodes |->
                          IF k = n THEN mailbox[n] \ (dm \cup um)
                          ELSE IF k \in incoming[n]
                               THEN mailbox[k] \cup {UpMsg(n, Reply(k), Prune(k))}
                               ELSE mailbox[k]]
         /\ active' = IF selfPrune THEN [active EXCEPT ![n] = FALSE] ELSE active
         /\ incoming' = [incoming EXCEPT ![n] = IF selfPrune THEN {} ELSE newIn]
         /\ outgoing' = [outgoing EXCEPT ![n] = IF selfPrune THEN {} ELSE newOut]
         /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : DownSource(n) \/ DownOther(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
  /\ active   \in [Nodes -> BOOLEAN]
  /\ phase    \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox  \in [Nodes -> SUBSET Messages]

NeighborInv ==
  \A n \in Nodes :
    /\ incoming[n] \subseteq Neighbors(n)
    /\ outgoing[n] \subseteq Neighbors(n)
    /\ incoming[n] \cap outgoing[n] = {}

Finished ==
  \A n \in Nodes : active[n] => (incoming[n] = {} /\ outgoing[n] = {})

FinishIffTerminated == Finished <=> ~(ENABLED Next)

Liveness == <>Finished

=============================================================================