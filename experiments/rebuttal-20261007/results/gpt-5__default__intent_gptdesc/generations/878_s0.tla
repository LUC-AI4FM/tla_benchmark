--------------------------- MODULE RootedSpanningTree ---------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  NODES,    \* finite set of nodes
  E,        \* set of undirected edges (each element is a 2-element set {u,v})
  Root,     \* distinguished root node
  B         \* numeric bound, at least Cardinality(NODES)

ASSUME
  /\ NODES # {} /\ IsFiniteSet(NODES)
  /\ Root \in NODES
  /\ E \subseteq { {u, v} : u \in NODES, v \in NODES, u # v }
  /\ B \in Nat /\ B >= Cardinality(NODES)

\* Basic graph notions
Edge(u, v) == u \in NODES /\ v \in NODES /\ u # v /\ {u, v} \in E
Neighbors(n) == { m \in NODES : Edge(n, m) }

\* Distances are capped by B
DistRange == 0..B

\* Messages carry the sender's current distance
Msg == [src: NODES, dst: NODES, d: DistRange]

VARIABLES
  parent,   \* [NODES -> NODES]
  dist,     \* [NODES -> DistRange]
  inbox,    \* [NODES -> [NODES -> DistRange]]  (last heard distance of each neighbor)
  msgs      \* SUBSET Msg

vars == << parent, dist, inbox, msgs >>

\* Typing and basic well-formedness
TypeOK ==
  /\ parent \in [NODES -> NODES]
  /\ dist \in [NODES -> DistRange]
  /\ inbox \in [NODES -> [NODES -> DistRange]]
  /\ msgs \subseteq Msg
  /\ \A m \in msgs : Edge(m.src, m.dst)

\* Root initially announces distance 0 to its neighbors
RootInitMsgs == { [src |-> Root, dst |-> m, d |-> 0] : m \in Neighbors(Root) }

Init ==
  /\ TypeOK
  /\ dist = [n \in NODES |-> IF n = Root THEN 0 ELSE B]
  /\ parent = [n \in NODES |-> n]
  /\ inbox = [n \in NODES |-> [m \in NODES |-> B]]
  /\ msgs = RootInitMsgs

\* Utility: minimum of a nonempty finite set of natural numbers
MinNat(S) == CHOOSE m \in S : \A n \in S : m <= n

\* Local computation uses only received neighbor distances from inbox
Offers(n) ==
  { inbox[n][m] + 1 : m \in Neighbors(n) } \cup { IF n = Root THEN 0 ELSE B }

NextBest(n) == MinNat(Offers(n))

\* A node updates its distance/parent based solely on inbox information
Update(n) ==
  /\ n \in NODES
  /\ LET best == NextBest(n) IN
       /\ (best < dist[n] \/ (n = Root /\ dist[n] # 0))
       /\ dist' = [dist EXCEPT ![n] = best]
       /\ parent' =
            IF n = Root /\ best = 0 THEN
              [parent EXCEPT ![n] = n]
            ELSE IF best = B THEN
              [parent EXCEPT ![n] = n]
            ELSE
              [parent EXCEPT ![n] =
                CHOOSE m \in Neighbors(n) : inbox[n][m] + 1 = best]
       /\ msgs' = msgs \cup { [src |-> n, dst |-> m, d |-> best] : m \in Neighbors(n) }
       /\ inbox' = inbox

\* Asynchronous message delivery; nodes learn neighbors' distances only via messages
Deliver ==
  \E m \in msgs :
    /\ msgs' = msgs \ { m }
    /\ inbox' = [inbox EXCEPT ![m.dst][m.src] = m.d]
    /\ UNCHANGED << parent, dist >>

Next == Deliver \/ (\E n \in NODES : Update(n))

\* Quiescence: no messages in flight and no local update enabled at any node
Quiescent ==
  /\ msgs = {}
  /\ \A n \in NODES :
       /\ ~(NextBest(n) < dist[n])
       /\ (n # Root \/ dist[n] = 0)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Deliver)
  /\ \A n \in NODES : WF_vars(Update(n))

\* Graph-theoretic postcondition definitions
IsPath(s) ==
  /\ s \in Seq(NODES)
  /\ Len(s) >= 1
  /\ \A i \in 1..(Len(s)-1) : Edge(s[i], s[i+1])

PathsTo(n) ==
  { s \in Seq(NODES) :
      /\ IsPath(s)
      /\ s[1] = Root
      /\ s[Len(s)] = n
      /\ Len(s) <= B+1 }

Reachable(n) == PathsTo(n) # {}

GraphDist(n) ==
  IF Reachable(n)
    THEN MinNat({ Len(s) - 1 : s \in PathsTo(n) })
    ELSE B

RECURSIVE Anc(_,_)
Anc(n, k) == IF k = 0 THEN n ELSE Anc(parent[ n ], k-1)

\* Postcondition that must hold upon quiescence
Post ==
  \A n \in NODES :
    /\ dist[n] = GraphDist(n)
    /\ IF Reachable(n) THEN
         /\ (IF n = Root THEN parent[n] = Root ELSE Edge(n, parent[n]) /\ dist[parent[n]] = dist[n] - 1)
         /\ \E k \in 0..B : Anc(n, k) = Root
       ELSE
         /\ dist[n] = B
         /\ parent[n] = n

\* Safety: upon quiescence, the spanning-tree and distance conditions hold
Safety == [](Quiescent => Post)

\* Liveness/progress under the given fairness: the system eventually quiesces forever
Termination == <>[]Quiescent

=============================================================================