---------------------------- MODULE YoYoAllGraphs ----------------------------
EXTENDS TLC, Integers, FiniteSets

CONSTANTS Nodes, Edges

ASSUME NodesAssump == Nodes \subseteq Int /\ Nodes # {}

ASSUME EdgesAssump ==
  /\ Edges \subseteq SUBSET Nodes
  /\ \A e \in Edges : Cardinality(e) = 2

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

ReachableFrom(n) ==
  LET Reach[k \in 0..Cardinality(Nodes)] ==
        IF k = 0 THEN {n}
        ELSE Reach[k-1] \cup {m \in Nodes : \E p \in Reach[k-1] : {p, m} \in Edges}
  IN  Reach[Cardinality(Nodes)]

ASSUME ConnectedAssump == \A n \in Nodes : ReachableFrom(n) = Nodes

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES phase, incoming, outgoing, mailbox

vars == <<phase, incoming, outgoing, mailbox>>

Messages ==
  [phase : {"down"}, sndr : Nodes, val : Nodes] \cup
  [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]

downMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s, r)   == [phase |-> "up", sndr |-> s, reply |-> r]

TypeOK ==
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]

NeighborInv ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] = Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}

NoNewSource ==
  \A n \in Nodes : incoming[n] = {} => \A m \in Neighbors(n) : n < m

Init ==
  /\ phase = [n \in Nodes |-> "down"]
  /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
  /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
  /\ mailbox = [n \in Nodes |-> {}]

DownMsgs(n) == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
UpMsgs(n)   == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

\* A source starts the down phase by sending its own identifier.
DownSource(n) ==
  /\ phase[n] = "down"
  /\ incoming[n] = {}
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, n)}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

\* An internal node forwards the minimum received value.
DownInternal(n) ==
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ outgoing[n] # {}
  /\ LET dm == DownMsgs(n)
     IN  /\ {msg.sndr : msg \in dm} = incoming[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m \in outgoing[n]
                          THEN mailbox[m] \cup {downMsg(n, Min({msg.val : msg \in dm}))}
                          ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

\* A sink receives all values and immediately replies, reversing "no" edges.
DownSink(n) ==
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ outgoing[n] = {}
  /\ LET dm == DownMsgs(n)
     IN  /\ {msg.sndr : msg \in dm} = incoming[n]
         /\ LET mn   == Min({msg.val : msg \in dm})
                yesS == {m \in incoming[n] : downMsg(m, mn) \in dm}
                noS  == incoming[n] \ yesS
            IN  /\ mailbox' = [m \in Nodes |->
                                 IF m = n THEN mailbox[n] \ dm
                                 ELSE IF m \in yesS THEN mailbox[m] \cup {upMsg(n, "yes")}
                                 ELSE IF m \in noS THEN mailbox[m] \cup {upMsg(n, "no")}
                                 ELSE mailbox[m]]
                /\ incoming' = [incoming EXCEPT ![n] = yesS]
                /\ outgoing' = [outgoing EXCEPT ![n] = noS]
  /\ UNCHANGED phase

\* Up phase for sources and internal nodes: collect replies, reply, reverse edges.
UpNode(n) ==
  /\ phase[n] = "up"
  /\ LET um == UpMsgs(n)
         dm == DownMsgs(n)
     IN  /\ {msg.sndr : msg \in um} = outgoing[n]
         /\ LET noOut  == {msg.sndr : msg \in {x \in um : x.reply = "no"}}
                allYes == noOut = {}
                yesS   == IF allYes /\ dm # {}
                          THEN LET mn == Min({msg.val : msg \in dm})
                               IN  {m \in incoming[n] : downMsg(m, mn) \in dm}
                          ELSE {}
                noS    == incoming[n] \ yesS
            IN  /\ mailbox' = [m \in Nodes |->
                                 IF m = n THEN mailbox[n] \ (um \cup dm)
                                 ELSE IF m \in yesS THEN mailbox[m] \cup {upMsg(n, "yes")}
                                 ELSE IF m \in noS THEN mailbox[m] \cup {upMsg(n, "no")}
                                 ELSE mailbox[m]]
                /\ incoming' = [incoming EXCEPT ![n] = yesS \cup noOut]
                /\ outgoing' = [outgoing EXCEPT ![n] = (outgoing[n] \ noOut) \cup noS]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Step(n) == DownSource(n) \/ DownInternal(n) \/ DownSink(n) \/ UpNode(n)

Next == \E n \in Nodes : Step(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Nodes : WF_vars(Step(n))

Stabilized ==
  /\ \A n \in Nodes : (incoming[n] = {}) <=> (n = Min(Nodes))
  /\ \A n \in Nodes : \A msg \in mailbox[n] :
        msg.phase = "up" => msg.reply = "yes"

Liveness == <>[]Stabilized

=============================================================================