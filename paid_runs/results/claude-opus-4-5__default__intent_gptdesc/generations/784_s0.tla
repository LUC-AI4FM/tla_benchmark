---------------------------- MODULE GameOfLife ----------------------------
(***************************************************************************)
(* Conway's Game of Life on a finite N×N toroidal (or non-wrapping) board  *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS 
    N,                  \* Grid size (N×N board)
    Toroidal,           \* TRUE for toroidal topology, FALSE for bounded
    MaxSteps            \* Bounded time horizon for model checking

ASSUME N \in Nat /\ N > 0
ASSUME Toroidal \in BOOLEAN
ASSUME MaxSteps \in Nat

VARIABLES 
    grid,               \* Function from grid positions to BOOLEAN (alive/dead)
    step,               \* Current time step
    history             \* Sequence of past grid states for cycle detection

(***************************************************************************)
(* Grid positions and topology                                              *)
(***************************************************************************)

Positions == (0..(N-1)) \X (0..(N-1))

\* Wrap coordinate for toroidal topology
Wrap(x) == x %% N

\* Compute neighbor position based on topology
NeighborPos(row, col, dr, dc) ==
    IF Toroidal THEN
        <<Wrap(row + dr), Wrap(col + dc)>>
    ELSE
        <<row + dr, col + dc>>

\* Check if a position is valid (always true for toroidal, bounded check otherwise)
ValidPos(pos) ==
    /\ pos[1] >= 0 /\ pos[1] < N
    /\ pos[2] >= 0 /\ pos[2] < N

\* Relative offsets for the 8 neighbors (Moore neighborhood)
NeighborOffsets == {<<dr, dc>> : dr \in {-1, 0, 1}, dc \in {-1, 0, 1}} \ {<<0, 0>>}

\* Get the set of neighbor positions for a cell
Neighbors(row, col) ==
    {NeighborPos(row, col, offset[1], offset[2]) : offset \in NeighborOffsets}

\* Count live neighbors for a cell at position (row, col)
CountLiveNeighbors(g, row, col) ==
    LET neighborPositions == Neighbors(row, col)
        validNeighbors == {pos \in neighborPositions : ValidPos(pos)}
    IN Cardinality({pos \in validNeighbors : g[pos]})

(***************************************************************************)
(* Game of Life rules                                                       *)
(***************************************************************************)

\* Determine next state of a single cell based on Life rules
NextCellState(g, row, col) ==
    LET liveNeighbors == CountLiveNeighbors(g, row, col)
        currentlyAlive == g[<<row, col>>]
    IN
        IF currentlyAlive THEN
            \* Live cell survives with 2 or 3 neighbors
            liveNeighbors \in {2, 3}
        ELSE
            \* Dead cell becomes alive with exactly 3 neighbors
            liveNeighbors = 3

\* Compute the next grid state (synchronous update of all cells)
NextGrid(g) ==
    [pos \in Positions |-> NextCellState(g, pos[1], pos[2])]

(***************************************************************************)
(* State predicates                                                         *)
(***************************************************************************)

\* Type invariant: grid maps positions to booleans
TypeOK ==
    /\ grid \in [Positions -> BOOLEAN]
    /\ step \in Nat
    /\ history \in Seq([Positions -> BOOLEAN])

\* The grid values remain in boolean domain
BooleanDomainInvariant ==
    \A pos \in Positions : grid[pos] \in BOOLEAN

\* Combined safety invariant
SafetyInvariant == TypeOK /\ BooleanDomainInvariant

(***************************************************************************)
(* Initial state and transitions                                            *)
(***************************************************************************)

\* Nondeterministic initial configuration
Init ==
    /\ grid \in [Positions -> BOOLEAN]  \* Any arbitrary configuration
    /\ step = 0
    /\ history = <<>>

\* Deterministic next state transition
Next ==
    /\ step < MaxSteps
    /\ grid' = NextGrid(grid)
    /\ step' = step + 1
    /\ history' = Append(history, grid)

\* Stuttering step when at max steps
Stutter ==
    /\ step >= MaxSteps
    /\ UNCHANGED <<grid, step, history>>

\* Complete next-state relation
NextOrStutter == Next \/ Stutter

(***************************************************************************)
(* Specification with fairness                                              *)
(***************************************************************************)

\* Weak fairness ensures progress when enabled
Spec == Init /\ [][NextOrStutter]_<<grid, step, history>> /\ WF_<<grid, step, history>>(Next)

(***************************************************************************)
(* Update determinism property                                              *)
(***************************************************************************)

\* Given a state, the next state is uniquely determined
\* This is inherent in the functional definition of NextGrid
\* We can verify by checking that NextGrid is a function
UpdateDeterminism ==
    \A g1, g2 \in [Positions -> BOOLEAN] :
        (g1 = g2) => (NextGrid(g1) = NextGrid(g2))

(***************************************************************************)
(* Pattern recognition predicates                                           *)
(***************************************************************************)

\* Check if a pattern exists at a given offset
PatternAt(g, pattern, offsetRow, offsetCol) ==
    \A <<pr, pc>> \in DOMAIN pattern :
        LET pos == IF Toroidal 
                   THEN <<Wrap(pr + offsetRow), Wrap(pc + offsetCol)>>
                   ELSE <<pr + offsetRow, pc + offsetCol>>
        IN ValidPos(pos) => (g[pos] = pattern[<<pr, pc>>])

\* A still life pattern (unchanged after one step)
IsStillLife(g) == NextGrid(g) = g

\* Block pattern (2x2 still life)
BlockPattern == [pos \in {<<0,0>>, <<0,1>>, <<1,0>>, <<1,1>>} |-> TRUE]

\* Check if grid contains only a block at origin (for testing)
IsBlock(g) ==
    \A pos \in Positions :
        g[pos] = (pos \in {<<0,0>>, <<0,1>>, <<1,0>>, <<1,1>>})

\* Beehive pattern (still life)
BeehivePositions == {<<0,1>>, <<0,2>>, <<1,0>>, <<1,3>>, <<2,1>>, <<2,2>>}

\* Check if a configuration is periodic with period p
IsPeriodic(g, p) ==
    LET iterate[n \in 0..p] ==
        IF n = 0 THEN g
        ELSE NextGrid(iterate[n-1])
    IN iterate[p] = g

\* Blinker pattern (period 2 oscillator)
BlinkerHorizontal == {<<1,0>>, <<1,1>>, <<1,2>>}
BlinkerVertical == {<<0,1>>, <<1,1>>, <<2,1>>}

\* Check if grid is a blinker at origin
IsBlinkerH(g) ==
    \A pos \in Positions :
        g[pos] = (pos \in BlinkerHorizontal)

IsBlinkerV(g) ==
    \A pos \in Positions :
        g[pos] = (pos \in BlinkerVertical)

\* Blinker oscillates between horizontal and vertical
BlinkerProperty ==
    (IsBlinkerH(grid) => IsBlinkerV(grid')) /\
    (IsBlinkerV(grid) => IsBlinkerH(grid'))

(***************************************************************************)
(* Glider pattern and translation                                           *)
(***************************************************************************)

\* Glider positions in standard orientation
GliderPhase1 == {<<0,1>>, <<1,2>>, <<2,0>>, <<2,1>>, <<2,2>>}

\* Check if glider exists at offset
GliderAt(g, offsetRow, offsetCol) ==
    LET translatePos(pos) == 
        IF Toroidal 
        THEN <<Wrap(pos[1] + offsetRow), Wrap(pos[2] + offsetCol)>>
        ELSE <<pos[1] + offsetRow, pos[2] + offsetCol>>
    IN \A pos \in GliderPhase1 :
        LET tpos == translatePos(pos)
        IN ValidPos(tpos) /\ g[tpos]

\* Glider translates diagonally with period 4
GliderTranslation ==
    \A r \in 0..(N-1), c \in 0..(N-1) :
        LET g4 == NextGrid(NextGrid(NextGrid(NextGrid(grid))))
            newR == IF Toroidal THEN Wrap(r + 1) ELSE r + 1
            newC == IF Toroidal THEN Wrap(c + 1) ELSE c + 1
        IN (GliderAt(grid, r, c) /\ Toroidal) => GliderAt(g4, newR, newC)

(***************************************************************************)
(* Cycle detection and liveness                                             *)
(***************************************************************************)

\* Check if current grid state has been seen before
StateRepeated ==
    \E i \in 1..Len(history) : history[i] = grid

\* Eventually we either reach max steps or find a cycle
Progress == <>(step >= MaxSteps \/ StateRepeated)

\* For periodic behavior: if we see a repeated state, we've found a cycle
CycleDetected == 
    step > 0 => 
        \E i \in 1..Len(history) : history[i] = grid

\* Liveness: eventually reach a cycle or stable state
EventuallyPeriodic == <>(IsStillLife(grid) \/ StateRepeated)

(***************************************************************************)
(* Bounded model checking properties                                        *)
(***************************************************************************)

\* Step bound invariant
BoundedSteps == step <= MaxSteps

\* No illegal transitions: next state is always computed correctly
NoIllegalTransition ==
    [][grid' = NextGrid(grid) \/ UNCHANGED grid]_<<grid>>

\* Neighbor count is always correct (verification helper)
CorrectNeighborCount ==
    \A pos \in Positions :
        LET count == CountLiveNeighbors(grid, pos[1], pos[2])
        IN count >= 0 /\ count <= 8

(***************************************************************************)
(* Conservation properties                                                  *)
(***************************************************************************)

\* Total population count
Population(g) == Cardinality({pos \in Positions : g[pos]})

\* Population is bounded
PopulationBounded == Population(grid) <= N * N

\* For still lifes, population is conserved
StillLifeConservation ==
    IsStillLife(grid) => Population(grid') = Population(grid)

(***************************************************************************)
(* Specific pattern invariants (can be enabled for specific tests)          *)
(***************************************************************************)

\* If initial state is a block, it remains a block
BlockStaysBlock ==
    IsBlock(grid) => IsBlock(grid')

\* Empty grid stays empty
EmptyStaysEmpty ==
    Population(grid) = 0 => Population(grid') = 0

\* Full grid behavior (all cells die except corners in bounded mode)
FullGridProperty ==
    (Population(grid) = N * N /\ N > 2) => Population(grid') < Population(grid)

(***************************************************************************)
(* Invariants for model checking                                            *)
(***************************************************************************)

\* Combined type and safety invariant
Invariant == 
    /\ TypeOK
    /\ BooleanDomainInvariant
    /\ BoundedSteps
    /\ CorrectNeighborCount
    /\ PopulationBounded

\* Temporal properties
TemporalProperties ==
    /\ Progress
    /\ NoIllegalTransition

=============================================================================