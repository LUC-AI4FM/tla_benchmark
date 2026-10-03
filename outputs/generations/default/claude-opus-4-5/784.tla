---------------------------- MODULE GameOfLife ----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

VARIABLES grid

Pos == (0..(N-1)) \X (0..(N-1))

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + SumSet(f, S \ {x})

IsAlive(x, y) ==
    IF x >= 0 /\ x < N /\ y >= 0 /\ y < N
    THEN grid[<<x, y>>]
    ELSE FALSE

NeighborOffsets == {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
                    <<0, -1>>,            <<0, 1>>,
                    <<1, -1>>,  <<1, 0>>,  <<1, 1>>}

Neighbors(x, y) == {<<x + d[1], y + d[2]>> : d \in NeighborOffsets}

LiveNeighborCount(x, y) ==
    LET neighborSet == Neighbors(x, y)
        aliveFunc == [p \in neighborSet |-> IF IsAlive(p[1], p[2]) THEN 1 ELSE 0]
    IN SumSet(aliveFunc, neighborSet)

NextCellState(x, y) ==
    LET count == LiveNeighborCount(x, y)
        alive == grid[<<x, y>>]
    IN IF alive
       THEN count = 2 \/ count = 3
       ELSE count = 3

Init == grid \in [Pos -> BOOLEAN]

Next == grid' = [p \in Pos |-> NextCellState(p[1], p[2])]

Spec == Init /\ [][Next]_grid

TypeInvariant == grid \in [Pos -> BOOLEAN]

=============================================================================