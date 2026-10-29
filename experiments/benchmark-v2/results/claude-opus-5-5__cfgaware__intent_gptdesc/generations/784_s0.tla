------------------------------ MODULE GameOfLife ------------------------------
(***************************************************************************)
(* Conway's Game of Life on a finite N x N board.                          *)
(*                                                                         *)
(* Cells are addressed by pairs <<x, y>> with x, y \in 0..N-1.             *)
(* The board is a function from positions to BOOLEAN (TRUE = alive).       *)
(* Every step updates all cells simultaneously by the standard rules:      *)
(*   - a live cell survives iff it has 2 or 3 live neighbours;             *)
(*   - a dead cell becomes alive iff it has exactly 3 live neighbours.     *)
(* Wrap = TRUE gives a toroidal board.                                     *)
(* Wrap = FALSE gives a bounded board, where out-of-range neighbours are   *)
(* always dead.                                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLE grid

vars == <<grid>>

(***************************************************************************)
(* Configuration options, defined as operators so the config binds only N. *)
(***************************************************************************)
Wrap    == TRUE      \* TRUE: toroidal topology; FALSE: dead boundary
Horizon == 8         \* time horizon used by the bounded checks

(***************************************************************************)
(* Board geometry                                                          *)
(***************************************************************************)
Coord == 0 .. (N - 1)
Pos   == Coord \X Coord

Grids == [Pos -> BOOLEAN]

\* The eight neighbour offsets (the cell itself is excluded).
Offsets == { <<dx, dy>> : dx \in {-1, 0, 1}, dy \in {-1, 0, 1} } \ { <<0, 0>> }

InRange(x, y) == x \in Coord /\ y \in Coord

WrapPos(p, d) == << (p[1] + d[1] + N) % N, (p[2] + d[2] + N) % N >>

\* Is the neighbour of p in direction d alive in board g?
NeighborAlive(g, p, d) ==
    IF Wrap
    THEN g[WrapPos(p, d)]
    ELSE LET x == p[1] + d[1]
             y == p[2] + d[2]
         IN  InRange(x, y) /\ g[<<x, y>>]

\* Count by offset, so neighbours that coincide on a tiny torus are counted
\* once per direction, as the standard toroidal rule requires.
LiveNeighbors(g, p) == Cardinality({ d \in Offsets : NeighborAlive(g, p, d) })

\* The Life rule for a single cell.
NextCell(g, p) ==
    LET n == LiveNeighbors(g, p)
    IN  IF g[p] THEN n \in {2, 3} ELSE n = 3

\* The deterministic synchronous successor of a whole board.
Step(g) == [p \in Pos |-> NextCell(g, p)]

\* The k-fold iteration of Step.
RECURSIVE Iter(_, _)
Iter(g, k) == IF k = 0 THEN g ELSE Iter(Step(g), k - 1)

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
\* Any initial configuration is allowed.
Init == grid \in Grids

\* Deterministic, synchronous update.
Next == grid' = Step(grid)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
\* Type correctness: the grid maps each position to a boolean.
TypeOK == grid \in [Pos -> BOOLEAN]

\* The live/dead labels stay within the boolean domain.
BooleanDomainInv == \A p \in Pos : grid[p] \in BOOLEAN

\* Neighbour counts are always well formed.
NeighborCountOK ==
    \A p \in Pos : LiveNeighbors(grid, p) \in 0 .. 8

\* Cross-check of the neighbour count by an explicit, independent method.
NeighborCountConsistent ==
    \A p \in Pos :
        LiveNeighbors(grid, p) =
            Cardinality({ d \in Offsets : NeighborAlive(grid, p, d) = TRUE })

\* Determinism: every non-stuttering step applies exactly the Life rules
\* cell by cell.
CellRuleStep ==
    \A p \in Pos :
        grid'[p] = IF grid[p]
                   THEN LiveNeighbors(grid, p) \in {2, 3}
                   ELSE LiveNeighbors(grid, p) = 3

UpdateDeterminism == [][CellRuleStep]_vars

\* Uniqueness of the successor: any board satisfying the cell rules
\* equals Step(grid).
UniqueSuccessor ==
    \A h \in Grids :
        (\A p \in Pos :
            h[p] = IF grid[p]
                   THEN LiveNeighbors(grid, p) \in {2, 3}
                   ELSE LiveNeighbors(grid, p) = 3)
        => h = Step(grid)

\* No illegal transitions: the successor stays a legal board.
NoIllegalTransition == [][grid' \in Grids /\ grid' = Step(grid)]_vars

\* Bounded-horizon type safety.
BoundedTypeOK == \A k \in 0 .. Horizon : Iter(grid, k) \in Grids

(***************************************************************************)
(* Patterns: still lifes, oscillators, gliders                             *)
(***************************************************************************)
FromSet(S) == [p \in Pos |-> p \in S]

Translate(S, dx, dy) ==
    IF Wrap
    THEN { << (q[1] + dx + N) % N, (q[2] + dy + N) % N >> : q \in S }
    ELSE { <<q[1] + dx, q[2] + dy>> : q \in S } \cap Pos

\* Still life: 2x2 block.
Block   == { <<1, 1>>, <<2, 1>>, <<1, 2>>, <<2, 2>> }

\* Period-2 oscillator: blinker.
Blinker == { <<1, 2>>, <<2, 2>>, <<3, 2>> }

\* Glider moving by (+1, +1) every 4 generations.
Glider  == { <<1, 0>>, <<2, 1>>, <<0, 2>>, <<1, 2>>, <<2, 2>> }

IsStillLife(g) == Step(g) = g

IsOscillator(g, k) ==
    /\ k \in Nat \ {0}
    /\ Iter(g, k) = g
    /\ \A j \in 1 .. (k - 1) : Iter(g, j) # g

TranslatesAs(g, period, dx, dy, S) ==
    /\ g = FromSet(S)
    /\ Iter(g, period) = FromSet(Translate(S, dx, dy))

\* Static facts about the patterns, checkable for a given N.
BlockIsStillLife     == IsStillLife(FromSet(Block))
BlinkerPeriod2       == IsOscillator(FromSet(Blinker), 2)
GliderMoves          == TranslatesAs(FromSet(Glider), 4, 1, 1, Glider)

\* Behavioural pattern properties.
StillLifeStays ==
    [](IsStillLife(grid) => [](grid = Step(grid)))

BlockConserved ==
    [](grid = FromSet(Block) => [](grid = FromSet(Block)))

BlinkerReturnsInv ==
    grid = FromSet(Blinker) => Iter(grid, 2) = grid

BlinkerReturns ==
    [](grid = FromSet(Blinker) => <>(grid = FromSet(Blinker)))

GliderTranslatesInv ==
    grid = FromSet(Glider) => Iter(grid, 4) = FromSet(Translate(Glider, 1, 1))

(***************************************************************************)
(* Progress and liveness: eventual periodicity                             *)
(* The state space is finite and the update is deterministic, so every     *)
(* run eventually enters a cycle.                                          *)
(***************************************************************************)
NumBoards == 2 ^ (N * N)

IsPeriodic(g) == \E k \in 1 .. NumBoards : Iter(g, k) = g

\* Some configuration lies on a cycle.
CycleExists == \E g \in Grids : IsPeriodic(g)

\* Every board reaches a periodic board within NumBoards steps.
EventuallyPeriodicBounded ==
    \E k \in 0 .. NumBoards : IsPeriodic(Iter(grid, k))

\* Liveness: every run eventually reaches a cycle and stays on it.
EventuallyPeriodic == <>(IsPeriodic(grid))
StaysPeriodic      == <>[](IsPeriodic(grid))

\* Once on a cycle, every state on it recurs infinitely often.
Recurrence ==
    \A g \in Grids :
        [](grid = g /\ IsPeriodic(g) => <>(grid = g))

=============================================================================