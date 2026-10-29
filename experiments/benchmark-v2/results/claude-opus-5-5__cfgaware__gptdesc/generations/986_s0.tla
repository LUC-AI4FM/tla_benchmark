---------------------------- MODULE YoYoPruning ----------------------------
EXTENDS TLC, Integers, FiniteSets

CONSTANTS Nodes, Edges

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

RECURSIVE Reach(_)
Reach(S) ==
  LET T == S \cup UNION {Neighbors(m) : m \in S}
  IN  IF T = S THEN S ELSE Reach(T)

IsConnected == \A n \in Nodes : Reach({n}) = Nodes

ASSUME
  /\ Nodes \subseteq Int
  /\ Edges \subseteq SUBSET Nodes
  /\ \A e \in Edges : Cardinality(e) = 2
  /\ IsConnected

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES active, phase, incoming, outgoing, mailbox

vars == <<active, phase, incoming, outgoing, mailbox>>

Messages ==
  [phase : {"down"}, sndr : Nodes, val : Nodes] \cup
  [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]

upMsgs(n) == {msg \in mailbox[n] : msg.phase = "up"}

\* down messages belonging to the current round (sent by incoming neighbors)
curDowns(n) == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}

\* down messages of the next round (sent by neighbors that reversed the edge)
nextDowns(n) == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in outgoing[n]}

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

\* A source starts the down phase by sending its identity to all out-neighbors.
DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] = {}
  /\ outgoing[n] # {}
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n]
                   THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> n]}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

\* An internal node or sink forwards the smallest received value.
DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] # {}
  /\ \A m \in incoming[n] : \E msg \in curDowns(n) : msg.sndr = m
  /\ LET v == Min({msg.val : msg \in curDowns(n)})
     IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n]
                       THEN mailbox[m] \cup {[phase |-> "down", sndr |-> n, val |-> v]}
                       ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

\* A source processes the replies of all its out-neighbors.
UpSource(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] = {}
  /\ {msg.sndr : msg \in upMsgs(n)} = outgoing[n]
  /\ LET ups == upMsgs(n)
         noSndrs == {u.sndr : u \in {x \in ups : ~x.prune /\ x.reply = "no"}}
         prunedOut == {u.sndr : u \in {x \in ups : x.prune}}
     IN  /\ incoming' = [incoming EXCEPT ![n] = noSndrs]
         /\ outgoing' = [outgoing EXCEPT ![n] = (@ \ noSndrs) \ prunedOut]
  /\ mailbox' = [mailbox EXCEPT ![n] = nextDowns(n)]
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ UNCHANGED active

\* An internal node or sink answers its in-neighbors after all out-neighbors replied,
\* possibly reversing or pruning edges, or pruning itself.
UpOther(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ incoming[n] # {}
  /\ {msg.sndr : msg \in upMsgs(n)} = outgoing[n]
  /\ LET downs == curDowns(n)
         ups == upMsgs(n)
         vals == {d.val : d \in downs}
         minVal == Min(vals)
         allYes == \A u \in ups : u.prune \/ u.reply = "yes"
         noSndrs == {u.sndr : u \in {x \in ups : ~x.prune /\ x.reply = "no"}}
         prunedOut == {u.sndr : u \in {x \in ups : x.prune}}
         keepers == {Min({d.sndr : d \in {x \in downs : x.val = v}}) : v \in vals}
         pruneSelf == outgoing[n] = {} /\ Cardinality(vals) = 1
         prunedIn == IF pruneSelf THEN incoming[n] ELSE incoming[n] \ keepers
         valOf(m) == (CHOOSE d \in downs : d.sndr = m).val
         answer(m) == IF valOf(m) = minVal /\ allYes THEN "yes" ELSE "no"
         noIn == {m \in incoming[n] \ prunedIn : answer(m) = "no"}
         reply(m) == [phase |-> "up", sndr |-> n, reply |-> answer(m),
                      prune |-> m \in prunedIn]
     IN  /\ mailbox' = [m \in Nodes |->
                          IF m = n
                          THEN (IF pruneSelf THEN {} ELSE nextDowns(n))
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup {reply(m)}
                               ELSE mailbox[m]]
         /\ IF pruneSelf
            THEN /\ active' = [active EXCEPT ![n] = FALSE]
                 /\ incoming' = [incoming EXCEPT ![n] = {}]
                 /\ outgoing' = [outgoing EXCEPT ![n] = {}]
            ELSE /\ active' = active
                 /\ incoming' = [incoming EXCEPT ![n] =
                                   ((@ \ prunedIn) \ noIn) \cup noSndrs]
                 /\ outgoing' = [outgoing EXCEPT ![n] =
                                   ((@ \ noSndrs) \ prunedOut) \cup noIn]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes :
          \/ DownSource(n)
          \/ DownOther(n)
          \/ UpSource(n)
          \/ UpOther(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Properties

NeighborInv ==
  \A n \in Nodes :
     /\ incoming[n] \cap outgoing[n] = {}
     /\ incoming[n] \cup outgoing[n] \subseteq Neighbors(n)
     /\ ~active[n] => (incoming[n] = {} /\ outgoing[n] = {})

NoNewSource ==
  [][\A n \in Nodes :
        (active'[n] /\ incoming[n] # {}) => incoming'[n] # {}]_vars

Terminated ==
  LET leader == Min(Nodes)
  IN  /\ \A n \in Nodes : active[n] <=> n = leader
      /\ incoming[leader] = {}
      /\ outgoing[leader] = {}

Liveness == <>Terminated

FinishIffTerminated == [](~(ENABLED Next) <=> Terminated)

=============================================================================