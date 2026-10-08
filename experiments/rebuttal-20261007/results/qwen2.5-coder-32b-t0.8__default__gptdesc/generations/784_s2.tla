------------------------------- MODULE ConwayLife -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLE grid

(*--algorithm ConwayLife
variables grid = [x \in 1..N, y \in 1..N |-> FALSE]
define
    Sum(S) == \E s \in SUBSET S : \A x \in S : (x \in s => s[x] \in Int) /\ (\A t \in SUBSET S : (\A x \in S : x \in t <=> x \in s) => t = s) /\ \Sum_{x \in s} s[x]
    OffGrid(x, y) == \/ x < 1 \/ x > N \/ y < 1 \/ y > N
    NeighborCount(x, y) == Sum({[dx, dy] \in {-1..1} \X {-1..1} : dx # 0 \/ dy # 0}: IF OffGrid(x+dx, y+dy) THEN FALSE ELSE grid[x+dx, y+dy])
    NextCellState(x, y) == CASE NeighborCount(x, y) = 3 -> TRUE
                             [] (NeighborCount(x, y) \in {2, 3}) /\ grid[x, y] -> TRUE
                             [] OTHER -> FALSE
end define

Init == grid \in [1..N -> [1..N -> BOOLEAN]]

Next ==
    /\ \E newGrid \in [1..N -> [1..N -> BOOLEAN]] :
        /\ \A x \in 1..N, y \in 1..N : newGrid[x, y] = NextCellState(x, y)
        /\ grid' = newGrid

Spec == Init /\ [][Next]_<<grid>>

=============================================================================