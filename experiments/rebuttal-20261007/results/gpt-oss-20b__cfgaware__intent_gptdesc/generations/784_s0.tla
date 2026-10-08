------------------------------ MODULE Life ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N

VARIABLES grid

(* Type correctness: each cell is a boolean *)
TypeOK == ∀ i,j ∈ 1..N : grid[i][j] ∈ BOOLEAN

(* Wrap index for toroidal board *)
Wrap(i) == ((i - 1) Mod N) + 1

(* Count live neighbors of cell (i,j) in grid g *)
NeighborCount(g, i, j) ==
    LET neighs == { <<Wrap(i+k), Wrap(j+l)>> : k,l ∈ {-1,0,1} /\ ~(k = 0 /\ l = 0) } IN
        SUM [p ∈ neighs |-> IF g[p[1]][p[2]] THEN 1 ELSE 0]

(* Next state of a single cell *)
NextCell(g, i, j) ==
    LET n == NeighborCount(g,i,j) IN
        IF g[i][j] THEN (n = 2 \/ n = 3)
        ELSE (n = 3)

(* Next grid according to Life rules *)
NextGrid(g) ==
    [i \in 1..N |-> [j \in 1..N |-> NextCell(g,i,j)] ]

(* Initial state: arbitrary assignment of booleans *)
Init == grid ∈ [1..N -> [1..N -> BOOLEAN]]

(* Deterministic next-state relation *)
Next == grid' = NextGrid(grid)

vars == <<grid>>

Spec == Init /\ [] [Next]_vars

=============================================================================