---- MODULE SpanningTree ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Nodes,   \* finite set of nodes
  Edge,    \* adjacency relation: subset of Nodes \X Nodes, symmetric, irreflexive
  Root,    \* distinguished root in Nodes
  Bound    \* natural number >= Cardinality(Nodes)

\* Neighborhood and adjacency
Adj(u, v) == <<u, v>> \in Edge
Neighbors(n) == { m \in Nodes : Adj(n, m) }

\* Message records
MsgSet ==
  { [from |-> u, to |-> v, dist |-> d] :
      u \in Nodes /\ v \in Nodes /\ d \in Nat /\
      d <= Bound /\ Adj(u, v)
  }

VARIABLES
  Parent,  \* function Nodes -> Nodes (parent pointer)
  Dist,    \* function Nodes -> Nat (hop distance, bounded by Bound)
  Msgs     \* set of in-flight messages (subset of MsgSet)

vars == << Parent, Dist, Msgs >>

\* Typing and static graph constraints
TypeOK ==
  /\ Root \in Nodes
  /\ Bound \in Nat
  /\ Bound >= Cardinality(Nodes)
  /\ Edge \subseteq Nodes \X Nodes
  /\ \A n \in Nodes : ~Adj(n, n)
  /\ \A u, v \in Nodes : Adj(u, v) <=> Adj(v, u)
  /\ Parent \in [Nodes -> Nodes]
  /\ Dist \in [Nodes -> Nat]
  /\ \A n \in Nodes : Dist[n] <= Bound
  /\ Msgs \subseteq MsgSet

\* Initial state:
\* - Root has distance 0 and is its own parent
\* - Others start unreachable (distance Bound) and parent self
\* - Root announces its distance to all neighbors
Init ==
  /\ Parent = [n \in Nodes |-> IF n = Root THEN Root ELSE n]
  /\ Dist   = [n \in Nodes |-> IF n = Root THEN 0 ELSE Bound]
  /\ Msgs   = { [from |-> Root, to |-> v, dist |-> 0] : v \in Neighbors(Root) }
  /\ TypeOK

\* One asynchronous delivery/processing step:
\* Deliver one message; if it improves the receiver's distance, update and
\* announce the new distance to all its neighbors.
Step ==
  \E m \in Msgs :
    LET n == m.to
        p == m.from
        d == m.dist
        imp == d + 1 < Dist[n]
        newDist == IF imp THEN d + 1 ELSE Dist[n]
        newParent == IF imp THEN p ELSE Parent[n]
        outgoing == IF imp THEN { [from |-> n, to |-> u, dist |-> newDist] : u \in Neighbors(n) } ELSE {}
    IN
      /\ Msgs'  = (Msgs \ {m}) \cup outgoing
      /\ Dist'  = [Dist EXCEPT ![n] = newDist]
      /\ Parent' = [Parent EXCEPT ![n] = newParent]

Next == Step

\* Quiescence: no more local steps (no in-flight messages)
Quiescent == Msgs = {}

\* Paths and graph-theoretic (shortest-hop) distance up to Bound
PathLen(v, k) ==
  \E s \in [1..(k+1) -> Nodes] :
    /\ s[1] = Root
    /\ s[k+1] = v
    /\ \A i \in 1..k : Adj(s[i], s[i+1])

HopLensTo(v) == { k \in 0..Bound : PathLen(v, k) }

MinNat(S) == CHOOSE m \in S : \A k \in S : m <= k

MinHop(v) ==
  LET S == HopLensTo(v) IN
    IF S = {} THEN Bound ELSE MinNat(S)

\* Postcondition at quiescence:
\* - Dist equals graph hop distance (or Bound if unreachable)
\* - Root has distance 0 and is its own parent
\* - For reachable non-root nodes, parent is a neighbor on a shortest path and
\*   has distance exactly one less.
GoodTree ==
  /\ Dist[Root] = 0
  /\ Parent[Root] = Root
  /\ \A n \in Nodes :
       IF HopLensTo(n) = {} THEN
         /\ Dist[n] = Bound
         /\ Parent[n] = n
       ELSE
         /\ Dist[n] = MinHop(n)
         /\ Dist[n] < Bound
         /\ IF n # Root THEN
              /\ Parent[n] \in Neighbors(n)
              /\ Dist[Parent[n]] = Dist[n] - 1
            ELSE TRUE

\* Safety: whenever the system quiesces, the postcondition holds
Safety == [] (Quiescent => GoodTree)

\* Liveness (under fairness below): the system eventually quiesces forever
Liveness == <>[] Quiescent

\* Full behavior with weak fairness of message delivery/processing
Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

====