------------------------------ MODULE GameOfLife ------------------------------

EXTENDS Integers, FiniteSets

CONSTANT N
ASSUME N \in Nat /\ N > 0

VARIABLES grid

X == 1..N
Y == 1..N
Positions == X \X Y

Offs == ({-1, 0, 1} \X {-1, 0, 1}) \ {<<0, 0>>}

Add(p, q) == << p[1] + q[1], p[2] + q[2] >>

InBounds(p) == p \in Positions

AliveAt(g, p) == IF InBounds(p) THEN g[p] ELSE FALSE

Neighbors(p) == { Add(p, off) : off \in Offs }

CountNeighbors(g, p) ==
  Cardinality({ q \in Neighbors(p) : AliveAt(g, q) })

NextCell(g, p) ==
  IF g[p]
    THEN CountNeighbors(g, p) = 2 \/ CountNeighbors(g, p) = 3
    ELSE CountNeighbors(g, p) = 3

Step(g) == [ p \in Positions |-> NextCell(g, p) ]

Init == grid \in [Positions -> BOOLEAN]

Next == grid' = Step(grid)

Spec == Init /\ []Next

TypeOK == grid \in [Positions -> BOOLEAN]

DeterministicRule ==
  \A g \in [Positions -> BOOLEAN] :
    \E! gp \in [Positions -> BOOLEAN] : gp = Step(g)

DeterministicAlongSpec == [](grid' = Step(grid))

THEOREM Spec => []TypeOK
THEOREM DeterministicRule
THEOREM Spec => DeterministicAlongSpec

=============================================================================