----------------------------- MODULE RandomizedSpanningTree -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Nodes,    \* finite, nonempty set of nodes
  Root,     \* distinguished root in Nodes
  Infinity  \* a value not in Nat, representing unreachable distance

ASSUME
  /\ Root \in Nodes
  /\ Nodes # {}
  /\ IsFinite(Nodes)
  /\ Infinity \notin Nat

\* Randomized undirected graph generation (constant-time, for TLC):
\* For each ordered pair (n,m) with n # m, choose a random boolean,
\* then symmetrize to obtain an undirected neighborhood.
RawOut ==
  [ n \in Nodes |->
      [ m \in (Nodes \ {n}) |->
          RandomElement({TRUE, FALSE}) ] ]

Neighbors(n) ==
  { m \in (Nodes \ {n}) : RawOut[n][m] \/ RawOut[m][n] }

Edges ==
  { {n, m} : n \in Nodes, m \in Neighbors(n) }

DistDom == Nat \cup {Infinity}

\* Order that extends the natural order with Infinity as the greatest element.
Less(x, y) ==
  IF x \in Nat THEN
    IF y \in Nat THEN x < y ELSE TRUE
  ELSE FALSE

VARIABLES
  mom,   \* parent pointers
  dist   \* distance estimates

vars == << mom, dist >>

Init ==
  /\ mom = [ n \in Nodes |-> n ]
  /\ dist = [ n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity ]

Next ==
  \E n \in Nodes, m \in Neighbors(n), d \in Nat:
    /\ Less(dist[m], dist[n])
    /\ Less(dist[m], d)
    /\ Less(d, dist[n])
    /\ mom'  = [ mom  EXCEPT ![n] = m ]
    /\ dist' = [ dist EXCEPT ![n] = d ]

TypeInv ==
  /\ mom \in [Nodes -> Nodes]
  /\ dist \in [Nodes -> DistDom]
  /\ dist[Root] = 0
  /\ mom[Root] = Root
  /\ \A n \in Nodes: mom[n] = n \/ mom[n] \in Neighbors(n)
  /\ \A n \in Nodes: dist[n] = Infinity \/ dist[n] \in Nat

IsEdge(u, v) == v \in Neighbors(u)

Reachable ==
  { v \in Nodes :
      \E s \in Seq(Nodes):
        /\ Len(s) >= 1
        /\ s[1] = Root
        /\ s[Len(s)] = v
        /\ \A i \in 1..(Len(s)-1): s[i+1] \in Neighbors(s[i]) }

\* A parent-chain from v to Root with per-step distance decrement 1
PC(v, s) ==
  /\ s \in Seq(Nodes)
  /\ Len(s) >= 1
  /\ s[1] = v
  /\ s[Len(s)] = Root
  /\ Len(s) <= Cardinality(Nodes)
  /\ \A i \in 1..(Len(s)-1):
       /\ s[i+1] = mom[s[i]]
       /\ s[i+1] \in Neighbors(s[i]]
       /\ dist[s[i]] \in Nat
       /\ dist[s[i]] = dist[s[i+1]] + 1

Post ==
  /\ dist[Root] = 0
  /\ mom[Root] = Root
  /\ \A v \in Reachable:
       \E s \in Seq(Nodes): PC(v, s)
  /\ \A v \in (Nodes \ Reachable):
       /\ dist[v] = Infinity
       /\ mom[v] = v

Quiescent == ~ENABLED Next

Safe == [](Quiescent => Post)

Live == <>Post

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

========================================================================================