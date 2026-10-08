---- MODULE RandomSpanningTree ----

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Root

VARIABLES mom, dist

(*--algorithm RandomSpanningTree
variables 
  mom \in [Nodes -> Nodes],
  dist \in [Nodes -> Nat];
begin
  Init;
  while TRUE do
    Next
  end while
end algorithm;*)

Init == /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE 1]

Edges ==
  LET RandomNeighbors(n) == {m \in (Nodes \ {n}): TLC!RandomElement({TRUE, FALSE})} 
  IN [n \in Nodes |-> RandomNeighbors(n)]

Next ==
  CHOOSE n \in Nodes: dist[n] > 0 /\
    /\ mom'[n] \in Edges[n]
    /\ dist'[mom'[n]] < dist[n]
    /\ dist'[n] = dist[mom'[n]] + 1
    /\ mom' = [mom EXCEPT ![n] = mom'[n]]
    /\ dist' = [dist EXCEPT ![n] = dist'[n]]

Spec ==
  WF_vars(Next) /\
  Init \/
  [][Next]_<<mom, dist>>

RootedSpanningTree ==
  LET Recur(n) == n = Root \/ (EXISTS p \in Nodes: mom[p] = n /\ Recur(p))
  IN FORALL n \in Nodes: Recur(n)

SafetyProperty == [](dist[Root] = 0 /\ FORALL n \in Nodes: dist[n] > 0 => mom[n] /= n) => RootedSpanningTree

LivenessProperty == <>[](RootedSpanningTree)

====