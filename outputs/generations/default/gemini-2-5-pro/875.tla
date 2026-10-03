---- MODULE RandomizedSpanningTree ----
EXTENDS Integers, FiniteSets, TLC, Sequences

CONSTANTS Nodes, Root

ASSUME IsFiniteSet(Nodes) /\ Root \in Nodes

VARIABLES mom, dist, Edges

vars == <<mom, dist, Edges>>

Infinity == -1

(*
 --algorithm a_spanning_tree
 variables
    mom = [n \in Nodes |-> n],
    dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity];
    Edges = LET AllPossibleUndirectedEdges == { {n1, n2} \in SUBSET Nodes : Cardinality({n1, n2}) = 2 }
            IN LET RandomUndirectedEdges == TLC!RandomElement(SUBSET AllPossibleUndirectedEdges)
               IN {<<n1, n2>> \in Nodes \X Nodes : {n1, n2} \in RandomUndirectedEdges};
 begin
  while \E n, m \in Nodes:
        <<n, m>> \in Edges
        /\ dist[m] /= Infinity
        /\ (dist[n] = Infinity \/ dist[m] + 1 < dist[n])
  do
    with n \in Nodes, m \in Nodes such
        <<n, m>> \in Edges
        /\ dist[m] /= Infinity
        /\ (dist[n] = Infinity \/ dist[m] + 1 < dist[n])
    do
        mom[n] := m;
        dist[n] := dist[m] + 1;
    end with;
  end while;
 end algorithm;
*)

TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Int]
    /\ \A n,m \in Nodes : <<n,m>> \in Edges <=> <<m,n>> \in Edges
    /\ dist[Root] = 0
    /\ \A n \in Nodes \ {Root} : dist[n] /= Infinity => dist[n] > 0
    /\ \A n \in Nodes \ {Root} : dist[n] /= Infinity => dist[mom[n]] < dist[n]

Init ==
    LET AllPossibleUndirectedEdges == { {n1, n2} \in SUBSET Nodes : Cardinality({n1, n2}) = 2 }
    IN LET RandomUndirectedEdges == TLC!RandomElement(SUBSET AllPossibleUndirectedEdges)
       IN /\ Edges = {<<n1, n2>> \in Nodes \X Nodes : {n1, n2} \in RandomUndirectedEdges}
          /\ mom = [n \in Nodes |-> n]
          /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE Infinity]

Next ==
    \/ \E n, m \in Nodes:
        /\ <<n, m>> \in Edges
        /\ dist[m] /= Infinity
        /\ (dist[n] = Infinity \/ dist[m] + 1 < dist[n])
        /\ mom' = [mom EXCEPT ![n] = m]
        /\ dist' = [dist EXCEPT ![n] = dist[m] + 1]
        /\ Edges' = Edges

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\*-----------------------------------------------------------------------------
\* Properties
\*-----------------------------------------------------------------------------

\* A path of k nodes (k-1 edges) from s to e
Path(s, e, k) == \E p \in Seq(Nodes):
                    /\ Len(p) = k
                    /\ p[1] = s
                    /\ p[k] = e
                    /\ \A i \in 1..(k-1) : <<p[i], p[i+1]>> \in Edges

Reachable(s, e) == \E k \in 2..Cardinality(Nodes) : Path(s, e, k)

ReachableFromRoot == {n \in Nodes : n = Root \/ Reachable(Root, n)}

\* The postcondition: a node has a finite distance iff it's reachable from the root.
Postcondition ==
    \A n \in Nodes: (n \in ReachableFromRoot) <=> (dist[n] /= Infinity)

\* Quiescence is the state where no more updates are possible.
Quiescence ==
    \A n, m \in Nodes :
      ~ ( <<n, m>> \in Edges
          /\ dist[m] /= Infinity
          /\ (dist[n] = Infinity \/ dist[m] + 1 < dist[n]) )

\* Safety: In any quiescent state, the postcondition must hold.
QuiescenceImpliesPostcondition == Quiescence => Postcondition

\* Liveness: The system eventually reaches a state where the postcondition holds.
EventuallyPostcondition == <>Postcondition

=============================================================================