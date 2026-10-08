MODULE Life
EXTENDS Naturals, Sequences, TLC

CONSTANT N \in Nat
CONSTANT TOROIDAL : BOOLEAN

VARIABLES grid, seen, cycleDetected

(* Type correctness *)
TypeOK == /\ grid ∈ [1..N -> 1..N -> BOOLEAN]
        /\ seen ⊆ [1..N -> 1..N -> BOOLEAN]
        /\ cycleDetected \in BOOLEAN

Wrap(i) == Mod(i-1, N)+1

Neighbors(i,j) ==
    IF TOROIDAL THEN
        { <<Wrap(i+di), Wrap(j+dj)>> : di ∈ {-1,0,1} /\ dj ∈ {-1,0,1}
          /\ ~(di=0 /\ dj=0) }
    ELSE
        { <<i+di, j+dj>> : di ∈ {-1,0,1} /\ dj ∈ {-1,0,1}
          /\ ~(di=0 /\ dj=0)
          /\ 1 <= i+di <= N
          /\ 1 <= j+dj <= N }

CountNeighbors(i,j) ==
    Cardinality({ <<x,y>> \in Neighbors(i,j) : grid[x][y] })

NextCell(i,j) ==
    LET n == CountNeighbors(i,j)
        alive == grid[i][j]
    IN
        IF alive THEN
            (n = 2 \/ n = 3)
        ELSE
            (n = 3)

NextGrid == [i \in 1..N, j \in 1..N |-> NextCell(i,j)]

(* Initial state *)
Init ==
    /\ TypeOK
    /\ grid \in [1..N -> 1..N -> BOOLEAN]
    /\ seen = {}
    /\ cycleDetected = FALSE

(* Update rule *)
Next ==
    /\ TypeOK
    /\ grid' = NextGrid
    /\ seen' = seen ∪ {grid}
    /\ cycleDetected' = cycleDetected \/ (∃ s \in seen : s = grid')

TypeInvariant == TypeOK

CycleLiveness == ◇(cycleDetected)

Spec == Init /\ [][Next]_<<grid,seen,cycleDetected>> /\ CycleLiveness

END MODULE Life