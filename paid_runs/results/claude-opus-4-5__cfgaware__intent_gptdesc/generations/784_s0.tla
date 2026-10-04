---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES grid, history

vars == <<grid, history>>

\* Grid positions
Pos == (0..(N-1)) \X (0..(N-1))

\* Wrap coordinate for toroidal topology
Wrap(x) == x %% N

\* Get neighbor coordinates with toroidal wrapping
Neighbors(r, c) == 
    { <<Wrap(r + dr), Wrap(c + dc)>> : 
        dr \in {-1, 0, 1}, dc \in {-1, 0, 1} } \ {<<r, c>>}

\* Count live neighbors for a cell
LiveNeighborCount(g, r, c) ==
    Cardinality({ pos \in Neighbors(r, c) : g[pos] = TRUE })

\* Apply Game of Life rules to determine next state of a cell
NextCellState(g, r, c) ==
    LET count == LiveNeighborCount(g, r, c)
        alive == g[<<r, c>>]
    IN IF alive 
       THEN count \in {2, 3}  \* Survival rule
       ELSE count = 3          \* Birth rule

\* Compute the next grid state (deterministic update)
NextGrid(g) ==
    [pos \in Pos |-> NextCellState(g, pos[1], pos[2])]

\* Type correctness invariant
TypeOK ==
    /\ grid \in [Pos -> BOOLEAN]
    /\ history \in Seq([Pos -> BOOLEAN])

\* Initial state: arbitrary assignment of alive/dead to all cells
Init ==
    /\ grid \in [Pos -> BOOLEAN]
    /\ history = <<grid>>

\* Next state: deterministic evolution according to Life rules
Next ==
    /\ grid' = NextGrid(grid)
    /\ history' = Append(history, grid')

\* Specification with weak fairness
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ============================================================================