---------------------------- MODULE YoYoPruning ----------------------------
(***************************************************************************)
(* The Yo-Yo leader election algorithm on a connected undirected graph,  *)
(* extended with pruning so that the algorithm terminates.               *)
(*                                                                         *)
(* At the start, every edge {m,n} is oriented from the smaller node to   *)
(* the larger node. Nodes without incoming edges are sources, nodes      *)
(* without outgoing edges are sinks, and all other nodes are internal.   *)
(*                                                                         *)
(* Down phase ("Yo-"): a source sends its identity to all of its         *)
(* out-neighbors. A non-source waits for values from all in-neighbors    *)
(* and forwards the minimum to its out-neighbors.                        *)
(*                                                                         *)
(* Up phase ("-Yo"): a node waits for replies from all out-neighbors.    *)
(* It then answers its in-neighbors. An in-neighbor that sent the        *)
(* minimum gets "yes", provided that no out-neighbor answered "no".      *)
(* Every other in-neighbor gets "no". Each edge on which "no" travels is *)
(* reversed.                                                              *)
(*                                                                         *)
(* Pruning has two rules:                                                 *)
(*  - If several in-neighbors send the same value, all of them except    *)
(*    one are asked to prune their edge.                                 *)
(*  - A sink that receives only a single value prunes itself together    *)
(*    with all of its incident edges.                                    *)
(*                                                                         *)
(* Eventually only the smallest node remains active, as an isolated      *)
(* leader.                                                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Neighbors(n) == {m \in Nodes : {m, n} \in Edges}

\* The set of nodes reachable from n in the original graph.
Reachable(n) ==
  LET R[k \in Nat] ==
        IF k = 0 THEN {n}
        ELSE R[k-1] \cup {m \in Nodes : \E p \in R[k-1] : {p, m} \in Edges}
  IN  R[Cardinality(Nodes)]

ASSUME
  /\ IsFiniteSet(Nodes)
  /\ Nodes # {}
  /\ Nodes \subseteq Nat
  /\ Edges \subseteq SUBSET Nodes
  /\ \A e \in Edges : Cardinality(e) = 2
  /\ \A n \in Nodes : Reachable(n) = Nodes      \* the graph is connected

VARIABLES
  active,    \* active[n]: FALSE once node n has been pruned
  phase,     \* "down" or "up"
  incoming,  \* node n's local view of its in-neighbors
  outgoing,  \* node n's local view of its out-neighbors
  mailbox    \* messages that were received but not yet processed

vars == <<active, phase, incoming, outgoing, mailbox>>

DownMsg(s, v) ==
  [phase |-> "down", sndr |-> s, val |-> v, reply |-> "none", prune |-> FALSE]

UpMsg(s, r, p) ==
  [phase |-> "up", sndr |-> s, val |-> 0, reply |-> r, prune |-> p]

Messages ==
  [phase : {"down", "up"}, sndr : Nodes, val : Nodes \cup {0},
   reply : {"none", "yes", "no"}, prune : BOOLEAN]

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

-----------------------------------------------------------------------------
(* Down phase. A source sends its own identity. A non-source waits for   *)
(* values from all in-neighbors and forwards their minimum.              *)
Down(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] \cup outgoing[n] # {}
  /\ LET dmsgs == {msg \in mailbox[n] :
                     msg.phase = "down" /\ msg.sndr \in incoming[n]}
         v     == IF incoming[n] = {} THEN n
                  ELSE Min({msg.val : msg \in dmsgs})
     IN  /\ {msg.sndr : msg \in dmsgs} = incoming[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m \in outgoing[n]
                          THEN mailbox[m] \cup {DownMsg(n, v)}
                          ELSE mailbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(* Up phase. The node waits for replies from all out-neighbors. It then *)
(* answers its in-neighbors, reverses or prunes edges, and returns to    *)
(* the down phase. A sink that receives a single value prunes itself.    *)
Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ LET dmsgs     == {msg \in mailbox[n] :
                         msg.phase = "down" /\ msg.sndr \in incoming[n]}
         umsgs     == {msg \in mailbox[n] :
                         msg.phase = "up" /\ msg.sndr \in outgoing[n]}
         vals      == {msg.val : msg \in dmsgs}
         minVal    == IF vals = {} THEN n ELSE Min(vals)
         valOf(m)  == (CHOOSE msg \in dmsgs : msg.sndr = m).val
         keep(v)   == Min({m \in incoming[n] : valOf(m) = v})
         prunedOut == {u.sndr : u \in {w \in umsgs : w.prune}}
         noOut     == {u.sndr : u \in {w \in umsgs : w.reply = "no" /\ ~w.prune}}
         selfPrune == /\ outgoing[n] = {}
                      /\ incoming[n] # {}
                      /\ Cardinality(vals) = 1
         pruneIn(m) == selfPrune \/ m # keep(valOf(m))
         answer(m)  == IF noOut = {} /\ valOf(m) = minVal THEN "yes" ELSE "no"
         prunedIn  == {m \in incoming[n] : pruneIn(m)}
         yesIn     == {m \in incoming[n] \ prunedIn : answer(m) = "yes"}
         noIn      == {m \in incoming[n] \ prunedIn : answer(m) = "no"}
     IN  /\ {msg.sndr : msg \in umsgs} = outgoing[n]
         /\ mailbox' = [m \in Nodes |->
                          IF m = n THEN mailbox[n] \ (dmsgs \cup umsgs)
                          ELSE IF m \in incoming[n]
                               THEN mailbox[m] \cup {UpMsg(n, answer(m), pruneIn(m))}
                               ELSE mailbox[m]]
         /\ active' = [active EXCEPT ![n] = ~selfPrune]
         /\ incoming' = [incoming EXCEPT ![n] =
                           IF selfPrune THEN {} ELSE yesIn \cup noOut]
         /\ outgoing' = [outgoing EXCEPT ![n] =
                           IF selfPrune THEN {}
                           ELSE noIn \cup (outgoing[n] \ (prunedOut \cup noOut))]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

Leader == Min(Nodes)

Terminated ==
  \A n \in Nodes :
     /\ active[n] <=> (n = Leader)
     /\ incoming[n] = {}
     /\ outgoing[n] = {}

\* Edges in local views stay within the original graph and are oriented.
EdgesConsistent ==
  \A n \in Nodes :
     /\ incoming[n] \cup outgoing[n] \subseteq Neighbors(n)
     /\ incoming[n] \cap outgoing[n] = {}
     /\ ~active[n] => incoming[n] \cup outgoing[n] = {}

\* When two active neighbors are both between rounds, their views agree.
ViewsAgree ==
  \A m, n \in Nodes :
     (active[m] /\ active[n] /\ phase[m] = "down" /\ phase[n] = "down")
       => (m \in outgoing[n] <=> n \in incoming[m])

\* Once a node is between rounds, its edges lead only to active nodes.
NoEdgesToPruned ==
  \A n \in Nodes :
     (active[n] /\ phase[n] = "down")
       => \A m \in incoming[n] \cup outgoing[n] : active[m]

\* The smallest node is never pruned and always stays a source.
MinIsSource == active[Leader] /\ incoming[Leader] = {}

\* At termination, the unique remaining node is the smallest one.
LeaderIsMin == Terminated => {n \in Nodes : active[n]} = {Leader}

Safety ==
  /\ TypeOK
  /\ EdgesConsistent
  /\ ViewsAgree
  /\ NoEdgesToPruned
  /\ MinIsSource
  /\ LeaderIsMin

\* The algorithm eventually terminates.
Liveness == <>Terminated

\* Termination and deadlock coincide.
DeadlockIffTerminated == [](Terminated <=> ~ENABLED Next)

\* Once terminated, the system stays terminated.
StableTermination == [](Terminated => []Terminated)

THEOREM Spec => []Safety
THEOREM Spec => Liveness /\ DeadlockIffTerminated /\ StableTermination
=============================================================================