---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    N,          \* board side length (N x N cells)
    Toroidal,   \* TRUE: wrap-around edges; FALSE: out-of-range neighbors are dead
    MaxSteps    \* bounded time horizon for model checking

ASSUME NAssumption        == N \in Nat \ {0}
ASSUME ToroidalAssumption == Toroidal \in BOOLEAN
ASSUME HorizonAssumption  == MaxSteps \in Nat

VARIABLES
    grid,   \* current configuration: Pos -> BOOLEAN (TRUE = alive)
    init,   \* the initial configuration, recorded for pattern properties
    step,   \* number of generations elapsed
    seen    \* set of configurations visited before the current one

vars == <<grid, init, step, seen>>

---------------------------------------------------------------------------
(* Board geometry                                                          *)
---------------------------------------------------------------------------

Coord == 0 .. (N - 1)
Pos   == Coord \X Coord
Grids == [Pos -> BOOLEAN]

Offsets == ({-1, 0, 1} \X {-1, 0, 1}) \ {<<0, 0>>}

\* Whether a neighbor offset from position p refers to an existing cell
InBoard(p, o) ==
    \/ Toroidal
    \/ /\ p[1] + o[1] \in Coord
       /\ p[2] + o[2] \in Coord

\* Position of a neighbor (only meaningful when InBoard(p, o))
NbPos(p, o) ==
    IF Toroidal
    THEN <<(p[1] + o[1]) % N, (p[2] + o[2]) % N>>
    ELSE <<p[1] + o[1], p[2] + o[2]>>

\* Primary neighbor count: counts offsets (so multiplicity is kept even
\* when N < 3 on a torus and several offsets reach the same cell).
LiveNeighbors(g, p) ==
    Cardinality({ o \in Offsets : InBoard(p, o) /\ g[NbPos(p, o)] })

\* Independent count used to cross-check LiveNeighbors (no miscounting).
Cell(g, x, y) ==
    IF Toroidal
    THEN g[<<x % N, y % N>>]
    ELSE IF x \in Coord /\ y \in Coord THEN g[<<x, y>>] ELSE FALSE

B2N(b) == IF b THEN 1 ELSE 0

ExplicitCount(g, p) ==
    LET x == p[1]
        y == p[2]
    IN    B2N(Cell(g, x - 1, y - 1)) + B2N(Cell(g, x, y - 1)) + B2N(Cell(g, x + 1, y - 1))
        + B2N(Cell(g, x - 1, y    ))                          + B2N(Cell(g, x + 1, y    ))
        + B2N(Cell(g, x - 1, y + 1)) + B2N(Cell(g, x, y + 1)) + B2N(Cell(g, x + 1, y + 1))

---------------------------------------------------------------------------
(* Life rules                                                              *)
---------------------------------------------------------------------------

LifeRule(alive, n) ==
    IF alive THEN n \in {2, 3} ELSE n = 3

NextGrid(g) == [p \in Pos |-> LifeRule(g[p], LiveNeighbors(g, p))]

RECURSIVE Iter(_, _)
Iter(g, k) == IF k = 0 THEN g ELSE Iter(NextGrid(g), k - 1)

\* Shift a configuration by (dx, dy) on the torus
Translate(g, dx, dy) ==
    [p \in Pos |-> g[<<(p[1] - dx) % N, (p[2] - dy) % N>>]]

FromSet(S) == [p \in Pos |-> p \in S]

---------------------------------------------------------------------------
(* Recognized patterns                                                     *)
---------------------------------------------------------------------------

BlockCells   == {<<1, 1>>, <<1, 2>>, <<2, 1>>, <<2, 2>>}          \* still life
BlinkerCells == {<<2, 1>>, <<2, 2>>, <<2, 3>>}                    \* period-2 oscillator
GliderCells  == {<<1, 0>>, <<2, 1>>, <<0, 2>>, <<1, 2>>, <<2, 2>>} \* moves (+1,+1) per 4 gens

BlockGrid   == FromSet(BlockCells)
BlinkerGrid == FromSet(BlinkerCells)
GliderGrid  == FromSet(GliderCells)

BlockFits   == N >= 4
BlinkerFits == N >= 5
GliderFits  == N >= 5 /\ Toroidal

---------------------------------------------------------------------------
(* Specification                                                           *)
---------------------------------------------------------------------------

\* Arbitrary (nondeterministic) initial configuration
Init ==
    /\ grid \in Grids
    /\ init = grid
    /\ step = 0
    /\ seen = {}

\* One synchronous, deterministic generation
Step ==
    /\ step < MaxSteps
    /\ grid' = NextGrid(grid)
    /\ init' = init
    /\ step' = step + 1
    /\ seen' = seen \cup {grid}

\* Horizon reached: the bounded run terminates (stutters)
Done ==
    /\ step = MaxSteps
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

---------------------------------------------------------------------------
(* Safety properties                                                       *)
---------------------------------------------------------------------------

\* Type correctness: the grid maps every position to a boolean
TypeOK ==
    /\ grid \in Grids
    /\ init \in Grids
    /\ step \in 0 .. MaxSteps
    /\ seen \subseteq Grids

\* Invariance: labels stay in the boolean domain
LabelsBoolean == \A p \in Pos : grid[p] \in BOOLEAN

\* No miscounted neighbors: two independent counting methods agree
NoMiscount ==
    \A p \in Pos :
        /\ LiveNeighbors(grid, p) = ExplicitCount(grid, p)
        /\ LiveNeighbors(grid, p) \in 0 .. 8

\* The current state is exactly the step-th iterate of the initial state
FollowsRule == grid = Iter(init, step)

\* Update determinism: every step produces exactly NextGrid(grid)
Determinism ==
    [][Step => grid' = NextGrid(grid)]_vars

\* Absence of illegal transitions: every cell obeys the Life rules
NoIllegalTransition ==
    [][Step => \A p \in Pos :
                  grid'[p] = LifeRule(grid[p], ExplicitCount(grid, p))]_vars

\* Only generation steps or terminal stuttering are possible
StepMonotone == [][step' = step + 1 \/ UNCHANGED vars]_vars

\* Still life: a block remains unchanged forever
StillLifeInvariant ==
    (BlockFits /\ init = BlockGrid) => grid = BlockGrid

\* Oscillator: the blinker returns to its initial configuration with period 2
OscillatorInvariant ==
    (BlinkerFits /\ init = BlinkerGrid) =>
        /\ (step % 2 = 0) => grid = BlinkerGrid
        /\ (step % 2 = 1) => grid # BlinkerGrid

\* Glider: translates by (+1, +1) every 4 generations on the torus
GliderInvariant ==
    (GliderFits /\ init = GliderGrid) =>
        /\ (step % 4 = 0) => grid = Translate(GliderGrid, step \div 4, step \div 4)
        /\ (step % 4 # 0) => grid # Translate(GliderGrid, step \div 4, step \div 4)

\* Static sanity checks on patterns (independent of behaviors)
PatternChecks ==
    /\ BlockFits   => NextGrid(BlockGrid) = BlockGrid
    /\ BlinkerFits => /\ Iter(BlinkerGrid, 2) = BlinkerGrid
                      /\ NextGrid(BlinkerGrid) # BlinkerGrid
    /\ GliderFits  => Iter(GliderGrid, 4) = Translate(GliderGrid, 1, 1)

---------------------------------------------------------------------------
(* Liveness / periodicity                                                  *)
---------------------------------------------------------------------------

CycleDetected == grid \in seen

\* By pigeonhole, a finite deterministic system revisits a state within
\* 2^(N*N) generations. This holds when MaxSteps >= 2^(N*N).
EventuallyRepeats == <>CycleDetected

\* Once a repeated state is reached, the run stays in the periodic regime
CycleIsStable == [](CycleDetected => []CycleDetected)

\* Recognized periodic patterns reach a repeated state (bounded check)
StillLifeRepeats ==
    (BlockFits /\ init = BlockGrid /\ MaxSteps >= 1) ~> CycleDetected
OscillatorRepeats ==
    (BlinkerFits /\ init = BlinkerGrid /\ MaxSteps >= 2) ~> CycleDetected

\* The bounded run always reaches its horizon
ReachesHorizon == <>(step = MaxSteps)

\* Existence of a cycle reachable from some initial configuration:
\* checking this invariant with TLC should yield a counterexample
\* (a witness trace) showing a repeated state.
NoCycleEver == ~CycleDetected

===========================================================================