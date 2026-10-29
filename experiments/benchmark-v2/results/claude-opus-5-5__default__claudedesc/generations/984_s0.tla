--------------------------- MODULE YoYoAllGraphs ---------------------------
(***************************************************************************)
(* The Yo-Yo leader election algorithm with pruning, checked over all      *)
(* undirected, loop-free, connected graphs on the nodes 1 .. N. Init picks *)
(* any connected subset of the complete edge set. Edges are first oriented *)
(* from lower to higher node identities.                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N
ASSUME NAssump == N \in Nat \ {0}

Nodes == 1 .. N

\* all undirected edges without self loops
AllEdges == {e \in SUBSET Nodes : Cardinality(e) = 2}

\* nodes reachable from S through edges in E
RECURSIVE Reach(_, _)
Reach(S, E) ==
  LET S2 == S \cup {m \in Nodes : \E n \in S : {m, n} \in E}
  IN  IF S2 = S THEN S ELSE Reach(S2, E)

Connected(E) == Reach({1}, E) = Nodes

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Messages ==
     [phase : {"down"}, sndr : Nodes, val : Nodes]
  \cup
     [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]

downMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s, r, p) == [phase |-> "up", sndr |-> s, reply |-> r, prune |-> p]

VARIABLES active, phase, incoming, outgoing, mailbox
vars == <<active, phase, incoming, outgoing, mailbox>>

-----------------------------------------------------------------------------
(* Auxiliary operators *)

\* kind of node, "isolated" nodes (no edges at all) never act
kind(n) ==
  IF incoming[n] = {} /\ outgoing[n] = {} THEN "isolated"
  ELSE IF incoming[n] = {} THEN "source"
  ELSE IF outgoing[n] = {} THEN "sink"
  ELSE "internal"

\* down messages of the current round: from current incoming neighbors
downMsgs(n) == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}

\* up messages from current outgoing neighbors
upMsgs(n) == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

valOf(n, s) == (CHOOSE msg \in downMsgs(n) : msg.sndr = s).val

replyOf(n, s) == CHOOSE msg \in upMsgs(n) : msg.sndr = s

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ phase \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox \in [Nodes -> SUBSET Messages]
  /\ \A n \in Nodes :
        /\ n \notin incoming[n]
        /\ n \notin outgoing[n]
        /\ incoming[n] \cap outgoing[n] = {}

NeighborInv ==
  \A m, n \in Nodes :
     /\ m \in incoming[n] => n \in outgoing[m]
     /\ m \in outgoing[n] =>
           \/ n \in incoming[m]
           \/ \E msg \in mailbox[n] :
                 /\ msg.phase = "up"
                 /\ msg.sndr = m
                 /\ (msg.reply = "no" \/ msg.prune)

\* the minimum node is the only active node, it has no remaining edges,
\* and there are no pending messages
Terminated ==
  /\ \A n \in Nodes : active[n] <=> n = Min(Nodes)
  /\ incoming[Min(Nodes)] = {}
  /\ outgoing[Min(Nodes)] = {}
  /\ \A n \in Nodes : mailbox[n] = {}

-----------------------------------------------------------------------------
(* Initial states: any connected graph *)

Init ==
  \E E \in SUBSET AllEdges :
     /\ Connected(E)
     /\ active = [n \in Nodes |-> TRUE]
     /\ phase = [n \in Nodes |-> "down"]
     /\ incoming = [n \in Nodes |-> {m \in Nodes : {m, n} \in E /\ m < n}]
     /\ outgoing = [n \in Nodes |-> {m \in Nodes : {m, n} \in E /\ m > n}]
     /\ mailbox = [n \in Nodes |-> {}]

-----------------------------------------------------------------------------
(* Down phase *)

\* sources start the down phase immediately and send their own identity
DownSource(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ kind(n) = "source"
  /\ mailbox' = [m \in Nodes |->
                   IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, n)}
                   ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

\* internal nodes and sinks wait for values from all incoming neighbors
\* and forward the minimum
DownOther(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ kind(n) \in {"internal", "sink"}
  /\ {msg.sndr : msg \in downMsgs(n)} = incoming[n]
  /\ LET min == Min({msg.val : msg \in downMsgs(n)})
     IN  mailbox' = [m \in Nodes |->
                       IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, min)}
                       ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

Down(n) == DownSource(n) \/ DownOther(n)

-----------------------------------------------------------------------------
(* Up phase *)

Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ kind(n) # "isolated"
  /\ {msg.sndr : msg \in upMsgs(n)} = outgoing[n]
  /\ LET vals == {valOf(n, s) : s \in incoming[n]}
         min == IF incoming[n] = {} THEN n ELSE Min(vals)
         \* for every value received, keep one sender, prune the others
         kept == {Min({s \in incoming[n] : valOf(n, s) = v}) : v \in vals}
         \* a sink that receives a single value is a leaf: prune it
         isLeaf == outgoing[n] = {} /\ Cardinality(vals) = 1
         pruneIn == IF isLeaf THEN incoming[n] ELSE incoming[n] \ kept
         anyNo == \E s \in outgoing[n] : replyOf(n, s).reply = "no"
         answer(s) == IF anyNo \/ valOf(n, s) # min THEN "no" ELSE "yes"
         noIn == {s \in incoming[n] \ pruneIn : answer(s) = "no"}
         yesIn == {s \in incoming[n] \ pruneIn : answer(s) = "yes"}
         prunedOut == {s \in outgoing[n] : replyOf(n, s).prune}
         noOut == {s \in outgoing[n] \ prunedOut : replyOf(n, s).reply = "no"}
         yesOut == outgoing[n] \ (prunedOut \cup noOut)
         consumed == downMsgs(n) \cup upMsgs(n)
     IN  /\ incoming' = [incoming EXCEPT ![n] = yesIn \cup noOut]
         /\ outgoing' = [outgoing EXCEPT ![n] = noIn \cup yesOut]
         /\ active' = [active EXCEPT ![n] = ~isLeaf]
         /\ phase' = [phase EXCEPT ![n] = "down"]
         /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ consumed
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup {upMsg(n, answer(m), m \in pruneIn)}
                               ELSE mailbox[m]]

-----------------------------------------------------------------------------
Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A n \in Nodes : WF_vars(Down(n)) /\ WF_vars(Up(n))

-----------------------------------------------------------------------------
(* Properties to check *)

FinishIffTerminated == (~ ENABLED Next) <=> Terminated

Liveness == <>Terminated

THEOREM Spec => []TypeOK
THEOREM Spec => []NeighborInv
THEOREM Spec => []FinishIffTerminated
THEOREM Spec => Liveness
=============================================================================