---------------------------- MODULE RandomizedSpanningTree ----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Nodes,
  Root,
  Inf

ASSUME /\ Root \in Nodes
       /\ Inf \notin Nat

(*
  Random undirected graph:
  For each node n, choose a random subset of the other nodes using TLC!RandomElement,
  then take the symmetric closure to obtain undirected edges as 2-element node sets.
*)
Edges ==
  LET DirNbrs == [ n \in Nodes |-> TLC!RandomElement(SUBSET (Nodes \ {n})) ]
      Pairs   == { p \in Nodes \X Nodes :
                      /\ p[1] # p[2]
                      /\ (p[2] \in DirNbrs[p[1]] \/ p[1] \in DirNbrs[p[2]]) }
  IN { {p[1], p[2]} : p \in Pairs }

Neighbors(n) == { m \in Nodes : {n, m} \in Edges }

DistVals == Nat \cup {Inf}

DistLess(x, y) ==
  \/ (x \in Nat) /\ (y = Inf)
  \/ (x \in Nat) /\ (y \in Nat) /\ x < y

DistStrictBetween(x, y, z) == DistLess(x, y) /\ DistLess(y, z)

VARIABLES mom, dist

vars == << mom, dist >>

Init ==
  /\ mom = [ n \in Nodes |-> n ]
  /\ dist = [ n \in Nodes |-> IF n = Root THEN 0 ELSE Inf ]

Next ==
  \E n \in Nodes:
    \E m \in Neighbors(n):
      /\ DistLess(dist[m], dist[n])
      /\ \E d \in Nat:
           /\ DistStrictBetween(dist[m], d, dist[n])
           /\ mom' = [ mom EXCEPT ![n] = m ]
           /\ dist' = [ dist EXCEPT ![n] = d ]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK == /\ mom \in [Nodes -> Nodes]
          /\ dist \in [Nodes -> DistVals]

RootOK == /\ mom[Root] = Root
          /\ dist[Root] = 0

Post ==
  /\ RootOK
  /\ \A n \in Nodes:
       IF dist[n] = Inf
       THEN mom[n] = n
       ELSE IF n = Root
            THEN TRUE
            ELSE /\ {n, mom[n]} \in Edges
                 /\ dist[mom[n]] \in Nat
                 /\ dist[n] = dist[mom[n]] + 1

Quiescent == ~Enabled Next

Safety == [](Quiescent => Post)

Liveness == <>Post

=============================================================================