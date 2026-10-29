---------------------------- MODULE EchoBroadcast ----------------------------
(***************************************************************************)
(* Echo (flood/echo, PIF) algorithm on a connected undirected network.     *)
(*                                                                         *)
(* A single initiator, chosen nondeterministically from Nodes in Init,     *)
(* floods a token to all its neighbours. A non-initiator does three        *)
(* things when it first receives the token:                                *)
(*   - it records the sender as its parent;                                *)
(*   - it forwards the token to all its other neighbours, exactly once;    *)
(*   - it later sends one echo to its parent, after it has heard from      *)
(*     every neighbour.                                                    *)
(* A token that arrives at a node that has already been visited counts as  *)
(* that neighbour's reply. The initiator terminates when it has heard      *)
(* from all of its neighbours.                                             *)
(*                                                                         *)
(* Links are reliable, asynchronous and point to point. Each directed      *)
(* link carries at most one message, so a set of in-transit messages       *)
(* models the network exactly.                                             *)
(*                                                                         *)
(* Example TLC model with 3 nodes:                                         *)
(*   Nodes       <- {n1, n2, n3}            (model values)                 *)
(*   NetworkSize <- 3                                                      *)
(*   NoNode      <- NoNode                  (model value)                  *)
(*   Edges       <- {<<n1,n2>>,<<n2,n1>>,<<n2,n3>>,<<n3,n2>>,              *)
(*                   <<n1,n3>>,<<n3,n1>>}                                  *)
(*   INVARIANTS  TypeOK EchoAtMostOnce NoDuplicateForward                  *)
(*               ParentTree TerminationCorrect SpanningTree                *)
(*   PROPERTIES  Termination AllEchoesReceived StartLeadsToTermination     *)
(*               TerminationStable                                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Nodes,        \* the set of distinct nodes (parameter)
    Edges,        \* the topology, as a set of ordered pairs (parameter)
    NetworkSize,  \* the expected number of nodes (parameter)
    NoNode        \* a value that is not a node ("no parent")

ASSUME NodesAssumptions ==
    /\ IsFiniteSet(Nodes)
    /\ Nodes # {}
    /\ NetworkSize \in Nat
    /\ Cardinality(Nodes) = NetworkSize
    /\ NoNode \notin Nodes

Nbrs(n) == { m \in Nodes : <<n, m>> \in Edges }

RECURSIVE ReachSet(_)
ReachSet(S) ==
    LET T == S \cup { m \in Nodes : \E k \in S : <<k, m>> \in Edges }
    IN  IF T = S THEN S ELSE ReachSet(T)

ASSUME TopologyAssumptions ==
    /\ Edges \subseteq Nodes \X Nodes
    /\ \A n \in Nodes : <<n, n>> \notin Edges                       \* no self-loops
    /\ \A n, m \in Nodes : <<n, m>> \in Edges => <<m, n>> \in Edges \* undirected
    /\ \A n \in Nodes : ReachSet({n}) = Nodes                       \* connected

Msg == [type : {"token", "echo"}, src : Nodes, dst : Nodes]

VARIABLES
    initiator,   \* the chosen initiator
    started,     \* has the initiator started the broadcast?
    terminated,  \* has the initiator detected global termination?
    visited,     \* visited[n]: n has seen the broadcast
    parent,      \* parent[n]: the node from which n first received the token
    rcvd,        \* rcvd[n]: neighbours from which n has received a message
    echoTo,      \* echoTo[n]: the set of nodes to which n has sent an echo
    fwdCount,    \* fwdCount[n]: how many times n has forwarded the broadcast
    msgs         \* messages in transit

vars == <<initiator, started, terminated, visited, parent, rcvd,
          echoTo, fwdCount, msgs>>

TypeOK ==
    /\ initiator \in Nodes
    /\ started \in BOOLEAN
    /\ terminated \in BOOLEAN
    /\ visited \in [Nodes -> BOOLEAN]
    /\ parent \in [Nodes -> Nodes \cup {NoNode}]
    /\ rcvd \in [Nodes -> SUBSET Nodes]
    /\ echoTo \in [Nodes -> SUBSET Nodes]
    /\ fwdCount \in [Nodes -> Nat]
    /\ msgs \subseteq Msg

Init ==
    /\ initiator \in Nodes
    /\ started = FALSE
    /\ terminated = FALSE
    /\ visited = [n \in Nodes |-> FALSE]
    /\ parent = [n \in Nodes |-> NoNode]
    /\ rcvd = [n \in Nodes |-> {}]
    /\ echoTo = [n \in Nodes |-> {}]
    /\ fwdCount = [n \in Nodes |-> 0]
    /\ msgs = {}

TokensFrom(n, S) == { [type |-> "token", src |-> n, dst |-> m] : m \in S }

(* The initiator starts the broadcast. *)
Start ==
    /\ ~started
    /\ started' = TRUE
    /\ visited' = [visited EXCEPT ![initiator] = TRUE]
    /\ fwdCount' = [fwdCount EXCEPT ![initiator] = @ + 1]
    /\ msgs' = msgs \cup TokensFrom(initiator, Nbrs(initiator))
    /\ UNCHANGED <<initiator, terminated, parent, rcvd, echoTo>>

(* Node n receives a token. It forwards the token only on its first       *)
(* receipt; any later token counts as the sender's reply.                 *)
ReceiveToken(n) ==
    \E m \in msgs :
        /\ m.dst = n
        /\ m.type = "token"
        /\ rcvd' = [rcvd EXCEPT ![n] = @ \cup {m.src}]
        /\ IF ~visited[n]
              THEN /\ visited' = [visited EXCEPT ![n] = TRUE]
                   /\ parent' = [parent EXCEPT ![n] = m.src]
                   /\ fwdCount' = [fwdCount EXCEPT ![n] = @ + 1]
                   /\ msgs' = (msgs \ {m}) \cup TokensFrom(n, Nbrs(n) \ {m.src})
              ELSE /\ msgs' = msgs \ {m}
                   /\ UNCHANGED <<visited, parent, fwdCount>>
        /\ UNCHANGED <<initiator, started, terminated, echoTo>>

(* Node n receives an echo from one of its children. *)
ReceiveEcho(n) ==
    \E m \in msgs :
        /\ m.dst = n
        /\ m.type = "echo"
        /\ rcvd' = [rcvd EXCEPT ![n] = @ \cup {m.src}]
        /\ msgs' = msgs \ {m}
        /\ UNCHANGED <<initiator, started, terminated, visited, parent,
                       echoTo, fwdCount>>

(* A non-initiator that has heard from all its neighbours sends one echo  *)
(* to its parent.                                                         *)
SendEcho(n) ==
    /\ n # initiator
    /\ visited[n]
    /\ echoTo[n] = {}
    /\ rcvd[n] = Nbrs(n)
    /\ echoTo' = [echoTo EXCEPT ![n] = @ \cup {parent[n]}]
    /\ msgs' = msgs \cup {[type |-> "echo", src |-> n, dst |-> parent[n]]}
    /\ UNCHANGED <<initiator, started, terminated, visited, parent,
                   rcvd, fwdCount>>

(* The initiator detects completion. *)
Terminate ==
    /\ started
    /\ ~terminated
    /\ rcvd[initiator] = Nbrs(initiator)
    /\ terminated' = TRUE
    /\ UNCHANGED <<initiator, started, visited, parent, rcvd, echoTo,
                   fwdCount, msgs>>

(* Stuttering after termination, so that TLC does not report a deadlock. *)
Done == terminated /\ UNCHANGED vars

Next ==
    \/ Start
    \/ \E n \in Nodes : ReceiveToken(n) \/ ReceiveEcho(n) \/ SendEcho(n)
    \/ Terminate
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

Echoed(n) == echoTo[n] # {}

(* No node sends an echo to more than one parent, and only to its parent. *)
EchoAtMostOnce ==
    \A n \in Nodes :
        /\ Cardinality(echoTo[n]) <= 1
        /\ echoTo[n] \subseteq {parent[n]}
        /\ (n = initiator => echoTo[n] = {})

(* No node forwards the broadcast more than once. *)
NoDuplicateForward == \A n \in Nodes : fwdCount[n] <= 1

(* Follow parent pointers from n for at most k steps. *)
RECURSIVE Anc(_, _)
Anc(n, k) ==
    IF k = 0 \/ n = initiator \/ n = NoNode
        THEN n
        ELSE Anc(parent[n], k - 1)

(* The parent pointers of visited nodes form a tree rooted at the         *)
(* initiator. Every pointer goes to a visited neighbour, and every chain  *)
(* of pointers reaches the root, so the pointers are acyclic.             *)
ParentTree ==
    /\ parent[initiator] = NoNode
    /\ \A n \in Nodes \ {initiator} :
          visited[n] =>
              /\ parent[n] \in Nbrs(n)
              /\ visited[parent[n]]
              /\ Anc(n, Cardinality(Nodes)) = initiator

(* Termination implies that every node has seen the broadcast, every      *)
(* non-initiator has echoed upstream, and no messages remain in transit.  *)
TerminationCorrect ==
    terminated =>
        /\ \A n \in Nodes : visited[n]
        /\ \A n \in Nodes \ {initiator} : Echoed(n)
        /\ msgs = {}

(* At termination the parent relation is a spanning tree rooted at the    *)
(* initiator.                                                             *)
SpanningTree ==
    terminated =>
        /\ \A n \in Nodes : visited[n]
        /\ ParentTree
        /\ Cardinality({ <<n, parent[n]>> : n \in Nodes \ {initiator} })
               = Cardinality(Nodes) - 1

Safety ==
    /\ TypeOK
    /\ EchoAtMostOnce
    /\ NoDuplicateForward
    /\ ParentTree
    /\ TerminationCorrect
    /\ SpanningTree

-----------------------------------------------------------------------------
(* Liveness properties *)

(* The initiator eventually hears from all of its neighbours. *)
AllEchoesReceived == <>(rcvd[initiator] = Nbrs(initiator))

(* Global termination. *)
Termination == <>terminated

StartLeadsToTermination == started ~> terminated

TerminationStable == [][terminated => terminated']_vars

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Termination /\ AllEchoesReceived /\ StartLeadsToTermination
=============================================================================