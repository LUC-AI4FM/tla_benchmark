---------------------------- MODULE YoYoAllGraphs ----------------------------
(***************************************************************************)
(* Yo-Yo leader election with pruning, checked over all undirected,        *)
(* loop-free, connected graphs on the nodes 1..N.                          *)
(***************************************************************************)
EXTENDS TLC, Integers, FiniteSets

CONSTANT N
ASSUME N \in Nat \ {0}

Nodes == 1 .. N

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* all possible undirected, loop-free edges
AllEdges == {e \in SUBSET Nodes : Cardinality(e) = 2}

RECURSIVE ReachFrom(_, _)
ReachFrom(E, S) ==
    LET S2 == S \cup {m \in Nodes : \E k \in S : {k, m} \in E}
    IN  IF S2 = S THEN S ELSE ReachFrom(E, S2)

IsConnected(E) == ReachFrom(E, {1}) = Nodes

ConnectedGraphs == {E \in SUBSET AllEdges : IsConnected(E)}

VARIABLES Edges, active, phase, incoming, outgoing, mailbox
vars == <<Edges, active, phase, incoming, outgoing, mailbox>>

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

Messages ==
    [phase : {"down"}, sndr : Nodes, val : Nodes] \cup
    [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]

downMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s, r, p) == [phase |-> "up", sndr |-> s, reply |-> r, prune |-> p]

-----------------------------------------------------------------------------
Init ==
    /\ Edges \in ConnectedGraphs
    /\ active = [n \in Nodes |-> TRUE]
    /\ phase = [n \in Nodes |-> "down"]
    /\ incoming = [n \in Nodes |-> {m \in Neighbors(n) : m < n}]
    /\ outgoing = [n \in Nodes |-> {m \in Neighbors(n) : m > n}]
    /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase. Sources send their own identity immediately; other nodes    *)
(* wait for down messages from all incoming neighbors and forward the min. *)
(***************************************************************************)
Down(n) ==
    /\ active[n]
    /\ phase[n] = "down"
    /\ IF incoming[n] = {}
       THEN /\ outgoing[n] # {}
            /\ mailbox' = [m \in Nodes |->
                              IF m \in outgoing[n]
                              THEN mailbox[m] \cup {downMsg(n, n)}
                              ELSE mailbox[m]]
       ELSE LET downMsgs == {msg \in mailbox[n] :
                                msg.phase = "down" /\ msg.sndr \in incoming[n]}
            IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
                /\ LET mn == Min({msg.val : msg \in downMsgs})
                   IN  mailbox' = [m \in Nodes |->
                                     IF m \in outgoing[n]
                                     THEN mailbox[m] \cup {downMsg(n, mn)}
                                     ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<Edges, active, incoming, outgoing>>

(***************************************************************************)
(* Up phase. A node waits for replies from all outgoing neighbors, then    *)
(* replies to its incoming neighbors, reversing edges with "no" replies,   *)
(* removing pruned edges, and deactivating if it is a lone sink.           *)
(***************************************************************************)
Up(n) ==
    /\ active[n]
    /\ phase[n] = "up"
    /\ LET upMsgs   == {msg \in mailbox[n] :
                           msg.phase = "up" /\ msg.sndr \in outgoing[n]}
           downMsgs == {msg \in mailbox[n] :
                           msg.phase = "down" /\ msg.sndr \in incoming[n]}
       IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
           /\ LET prunedOut == {msg.sndr : msg \in {mm \in upMsgs : mm.prune}}
                  noOut     == {msg.sndr : msg \in
                                  {mm \in upMsgs : mm.reply = "no" /\ ~mm.prune}}
                  yesOut    == outgoing[n] \ (noOut \cup prunedOut)
                  anyNo     == \E mm \in upMsgs : mm.reply = "no"
                  minVal    == IF downMsgs = {} THEN n
                               ELSE Min({msg.val : msg \in downMsgs})
                  minSndrs  == {msg.sndr : msg \in
                                  {mm \in downMsgs : mm.val = minVal}}
                  keep      == IF minSndrs = {} THEN {} ELSE {Min(minSndrs)}
                  loneSink  == outgoing[n] = {} /\ Cardinality(incoming[n]) = 1
                  pruneIn   == IF loneSink THEN incoming[n]
                               ELSE minSndrs \ keep
                  reply(s)  == IF anyNo \/ s \notin minSndrs THEN "no" ELSE "yes"
                  noIn      == {s \in incoming[n] \ pruneIn : reply(s) = "no"}
                  yesIn     == incoming[n] \ (pruneIn \cup noIn)
              IN  /\ mailbox' = [m \in Nodes |->
                                   IF m = n
                                   THEN mailbox[n] \ (upMsgs \cup downMsgs)
                                   ELSE IF m \in incoming[n]
                                        THEN mailbox[m] \cup
                                               {upMsg(n, reply(m), m \in pruneIn)}
                                        ELSE mailbox[m]]
                  /\ incoming' = [incoming EXCEPT ![n] = yesIn \cup noOut]
                  /\ outgoing' = [outgoing EXCEPT ![n] = noIn \cup yesOut]
                  /\ active' = [active EXCEPT ![n] = ~loneSink]
                  /\ phase' = [phase EXCEPT ![n] = "down"]
                  /\ UNCHANGED Edges

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(Down(n)) /\ WF_vars(Up(n))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ Edges \subseteq AllEdges
    /\ active \in [Nodes -> BOOLEAN]
    /\ phase \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox \in [Nodes -> SUBSET Messages]
    /\ \A n \in Nodes :
          /\ n \notin incoming[n] \cup outgoing[n]
          /\ incoming[n] \cap outgoing[n] = {}
          /\ incoming[n] \cup outgoing[n] \subseteq Neighbors(n)

NeighborInv ==
    \A m, n \in Nodes :
       /\ m \in outgoing[n] =>
             \/ n \in incoming[m]
             \/ \E msg \in mailbox[n] :
                   /\ msg.phase = "up"
                   /\ msg.sndr = m
                   /\ \/ msg.prune
                      \/ msg.reply = "no" /\ n \in outgoing[m]
       /\ n \in incoming[m] => m \in outgoing[n]

Terminated ==
    /\ \A n \in Nodes : active[n] <=> (n = Min(Nodes))
    /\ \A n \in Nodes : mailbox[n] = {}

FinishIffTerminated == (~ ENABLED Next) <=> Terminated

Liveness == <>Terminated

=============================================================================