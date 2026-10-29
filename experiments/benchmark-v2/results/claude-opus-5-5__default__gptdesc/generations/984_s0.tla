--------------------------- MODULE YoYoPruning ---------------------------
(***************************************************************************)
(* Yo-Yo leader election with pruning on an undirected, loop-free,         *)
(* connected graph over a fixed set of numbered nodes.                     *)
(* Initially each edge is oriented from the smaller to the larger node.    *)
(* Each round has a down phase and an up phase.                            *)
(*   - Down phase: sources send their identity to their outgoing           *)
(*     neighbors. Other nodes wait for values from all incoming neighbors  *)
(*     and forward the minimum to their outgoing neighbors.                *)
(*   - Up phase: sinks, and then internal nodes once they have heard from  *)
(*     all outgoing neighbors, reply to their incoming neighbors. A "yes"  *)
(*     goes to the senders of the minimum when no "no" was received;       *)
(*     every other neighbor gets "no". Edges along which "no" is sent are  *)
(*     reversed.                                                           *)
(*   - Pruning: a node that receives the same value from several incoming  *)
(*     neighbors keeps a single such edge and prunes the others. A sink    *)
(*     that received only one distinct value prunes all its edges and      *)
(*     becomes inactive.                                                   *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Nodes
ASSUME Nodes \subseteq Nat /\ Nodes # {} /\ IsFiniteSet(Nodes)

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES
  active,    \* active[n]: is node n still participating?
  phase,     \* phase[n] \in {"down","up"}
  incoming,  \* incoming[n]: neighbors with an edge oriented towards n
  outgoing,  \* outgoing[n]: neighbors with an edge oriented away from n
  mailbox    \* mailbox[n]: set of messages received by n but not processed

vars == <<active, phase, incoming, outgoing, mailbox>>

DownMsgs == [phase : {"down"}, sndr : Nodes, val : Nodes]
UpMsgs   == [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]
Messages == DownMsgs \cup UpMsgs

(***************************************************************************)
(* Graph-related definitions                                               *)
(***************************************************************************)
IsUndirectedGraph(nb) ==
  /\ \A m \in Nodes : m \notin nb[m]
  /\ \A m, k \in Nodes : k \in nb[m] <=> m \in nb[k]

IsConnected(nb) ==
  \A S \in SUBSET Nodes :
     (S # {} /\ S # Nodes) => \E m \in S, k \in Nodes \ S : k \in nb[m]

Neighbors(n) == incoming[n] \cup outgoing[n]

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
  /\ \E nb \in [Nodes -> SUBSET Nodes] :
        /\ IsUndirectedGraph(nb)
        /\ IsConnected(nb)
        /\ incoming = [n \in Nodes |-> {m \in nb[n] : m < n}]
        /\ outgoing = [n \in Nodes |-> {m \in nb[n] : m > n}]
  /\ active  = [n \in Nodes |-> TRUE]
  /\ phase   = [n \in Nodes |-> "down"]
  /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase                                                              *)
(***************************************************************************)
DownFrom(n) == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
UpFrom(n)   == {msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr \in outgoing[n]}

Down(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ Neighbors(n) # {}
  /\ \A m \in incoming[n] : \E msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr = m
  /\ LET v == IF incoming[n] = {} THEN n
              ELSE Min({msg.val : msg \in DownFrom(n)})
     IN  mailbox' = [k \in Nodes |->
                       IF k \in outgoing[n]
                       THEN mailbox[k] \cup {[phase |-> "down", sndr |-> n, val |-> v]}
                       ELSE mailbox[k]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(***************************************************************************)
(* Up phase, including edge reversal and pruning                           *)
(***************************************************************************)
Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ Neighbors(n) # {}
  /\ \A m \in outgoing[n] : \E msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr = m
  /\ LET dmsgs     == DownFrom(n)
         umsgs     == UpFrom(n)
         ValOf(m)  == (CHOOSE msg \in dmsgs : msg.sndr = m).val
         vals      == {ValOf(m) : m \in incoming[n]}
         minv      == IF vals = {} THEN n ELSE Min(vals)
         allYes    == \A msg \in umsgs : msg.reply = "yes"
         prunedOut == {msg.sndr : msg \in {u \in umsgs : u.prune}}
         noOut     == {msg.sndr : msg \in {u \in umsgs : u.reply = "no" /\ ~u.prune}}
         leaf      == outgoing[n] = {} /\ Cardinality(vals) = 1
         Keep(v)   == CHOOSE m \in incoming[n] : ValOf(m) = v
         prunedIn  == IF leaf THEN incoming[n]
                      ELSE {m \in incoming[n] : m # Keep(ValOf(m))}
         Reply(m)  == IF allYes /\ ValOf(m) = minv THEN "yes" ELSE "no"
         noIn      == {m \in incoming[n] \ prunedIn : Reply(m) = "no"}
         newIn     == (incoming[n] \ (prunedIn \cup noIn)) \cup noOut
         newOut    == (outgoing[n] \ (prunedOut \cup noOut)) \cup noIn
     IN  /\ mailbox' = [k \in Nodes |->
                          IF k = n THEN mailbox[n] \ (dmsgs \cup umsgs)
                          ELSE IF k \in incoming[n]
                               THEN mailbox[k] \cup
                                      {[phase |-> "up", sndr |-> n,
                                        reply |-> Reply(k), prune |-> k \in prunedIn]}
                               ELSE mailbox[k]]
         /\ incoming' = [incoming EXCEPT ![n] = newIn]
         /\ outgoing' = [outgoing EXCEPT ![n] = newOut]
         /\ active'   = [active EXCEPT ![n] = ~leaf]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
  /\ active   \in [Nodes -> BOOLEAN]
  /\ phase    \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox  \in [Nodes -> SUBSET Messages]

NoSelfLoops == \A n \in Nodes : n \notin Neighbors(n)

DisjointOrientation == \A n \in Nodes : incoming[n] \cap outgoing[n] = {}

InactiveIsolated == \A n \in Nodes : ~active[n] => Neighbors(n) = {}

SomeActive == \E n \in Nodes : active[n]

Inv == TypeOK /\ NoSelfLoops /\ DisjointOrientation /\ InactiveIsolated /\ SomeActive

(***************************************************************************)
(* Termination and liveness                                                *)
(***************************************************************************)
Termination == \A n \in Nodes : active[n] => Neighbors(n) = {}

Liveness == <>Termination

TerminationIffDeadlock == [](Termination <=> ~ENABLED Next)

=============================================================================